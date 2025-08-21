# -*- coding: utf-8 -*-
import threading
from http.server import HTTPServer, BaseHTTPRequestHandler

# Health check用のダミーWebサーバー
class HealthHandler(BaseHTTPRequestHandler):
    def do_GET(self):
        self.send_response(200)
        self.end_headers()
        self.wfile.write(b"OK")

def run_health_server():
    server = HTTPServer(("0.0.0.0", 8000), HealthHandler)
    server.serve_forever()

# 別スレッドで起動
threading.Thread(target=run_health_server, daemon=True).start()


import os
import json
import random
import sqlite3
import asyncio
from typing import Dict, List, Set, Any, Tuple, Optional

import math  # only used for formatting, not for rating
import discord
from discord.ext import commands, tasks
from discord.ui import View, Button

# ========= 設定 =========
TOKEN = os.getenv("DISCORD_TOKEN") or "YOUR_DISCORD_TOKEN_HERE"
GUILD_ID = 1405124702984470558
CATEGORY_ID = 1405124702984470559
# スレッドを作成する親チャンネル
PARENT_CHANNEL_ID = 1405124702984470559  # 実際のテキストチャンネルIDに置き換えてください


TEAM_SIZE = 4                                 # 4vs4
PLAYERS_NEEDED = TEAM_SIZE * 2                # 8人
TOTAL_GAMES = 5                               # 5試合
VOTE_THRESHOLD = 5                            # 8人中5票で進行
# DB_PATH = "match.db"
DB_PATH = os.getenv("DB_PATH", "/mnt/data/match.db")

MATCHMAKING_INTERVAL = 30

# ========= TrueSkill =========
# pip install trueskill
import trueskill
# TrueSkill の環境。必要に応じてパラメータを調整してください。
# デフォルト: mu=25, sigma≈8.333, beta=mu/6, tau=sigma/100, draw_probability=0.10
ts = trueskill.TrueSkill(
    mu=25.0,
    sigma=25.0 / 6,   # ← 初期不確実性を半分に抑える（8.33 → 4.17）
    beta=25.0 / 12,   # ← 2.08 に下げて変動幅を抑制
    tau=0.005,        # ← 時間経過による揺らぎもさらに小さく
    draw_probability=0.05
)



DEFAULT_MU = ts.mu
DEFAULT_SIGMA = ts.sigma
# ========================

intents = discord.Intents.default()
intents.members = True
bot = commands.Bot(command_prefix="!", intents=intents)

# ========= DB 接続とテーブル =========
conn = sqlite3.connect(DB_PATH)
cur = conn.cursor()
# 任意：ロック耐性を少し改善
cur.execute("PRAGMA journal_mode=WAL;")
cur.execute("PRAGMA synchronous=NORMAL;")

# users テーブル（TrueSkill: mu, sigma）
cur.execute("""
CREATE TABLE IF NOT EXISTS users (
    user_id INTEGER PRIMARY KEY,
    mu REAL,
    sigma REAL,
    wins INTEGER DEFAULT 0,
    games INTEGER DEFAULT 0
)
""")

# 既存DBからの移行（mu, sigma 列がNULLなら初期化）
cur.execute("SELECT name FROM sqlite_master WHERE type='table' AND name='users'")
if cur.fetchone():
    # 列の存在確認（古い列 str/rd/vol が残っていても無視）
    cur.execute("PRAGMA table_info(users)")
    cols = {row[1] for row in cur.fetchall()}
    if "mu" not in cols:
        try:
            cur.execute("ALTER TABLE users ADD COLUMN mu REAL")
        except sqlite3.OperationalError:
            pass
    if "sigma" not in cols:
        try:
            cur.execute("ALTER TABLE users ADD COLUMN sigma REAL")
        except sqlite3.OperationalError:
            pass
    # 既存ユーザーの mu/sigma を初期化（NULL のみに適用）
    cur.execute("UPDATE users SET mu = COALESCE(mu, ?), sigma = COALESCE(sigma, ?)",
                (DEFAULT_MU, DEFAULT_SIGMA))

cur.execute("""
CREATE TABLE IF NOT EXISTS matches (
    match_id INTEGER PRIMARY KEY,
    guild_id INTEGER,
    category_id INTEGER,
    lobby_id INTEGER,
    players TEXT,
    current_game INTEGER,
    votes TEXT,
    is_dummy INTEGER
)
""")

cur.execute("""
CREATE TABLE IF NOT EXISTS games (
    match_id INTEGER,
    game_num INTEGER,
    team_a TEXT,
    team_b TEXT,
    ch_a_id INTEGER,
    ch_b_id INTEGER
)
""")

cur.execute("""
CREATE TABLE IF NOT EXISTS waiting_players (
    id INTEGER PRIMARY KEY
)
""")

cur.execute("""
CREATE TABLE IF NOT EXISTS in_match_players (
    id INTEGER PRIMARY KEY
)
""")

cur.execute("""
CREATE TABLE IF NOT EXISTS reports (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    reporter_id INTEGER,
    target_id INTEGER,
    reason TEXT,
    match_id INTEGER,
    timestamp DATETIME DEFAULT CURRENT_TIMESTAMP
)
""")
conn.commit()

# ========= メモリ内データ =========
user_data: Dict[int, int] = {}  # 表示用（= mu の整数丸め）
waiting_players: List[int] = []
current_matches: Dict[int, Dict[str, Any]] = {}
in_match_players: Set[int] = set()

# ---- ダミー用メンバー ----
class DummyMember:
    def __init__(self, idx: int):
        self.id = -idx  # 負数IDで区別
        self.mention = f"Dummy{idx}"

# ========= ユーティリティ =========

def find_member_by_input(guild: discord.Guild, input_str: str | None, fallback_user: discord.User):
    """入力文字列からMemberを探す（display_name/username 部分一致、ID、メンション対応）。無指定なら自分"""
    if input_str is None:
        return guild.get_member(fallback_user.id)

    # メンション形式 <@1234>
    if input_str.startswith("<@") and input_str.endswith(">"):
        uid = input_str.strip("<@!>")
        if uid.isdigit():
            return guild.get_member(int(uid))

    # display_name / username 部分一致検索
    matches = [
        m for m in guild.members
        if not m.bot and (input_str.lower() in m.display_name.lower() or input_str.lower() in m.name.lower())
    ]
    if len(matches) == 1:
        return matches[0]
    elif len(matches) > 1:
        return matches  # 複数候補 → 呼び出し元で処理

    # 名前で見つからなかった場合のみ ID検索
    if input_str.isdigit():
        return guild.get_member(int(input_str))

    return None

# --- Thread/TextChannel ヘルパ ---
def get_textlike(guild: discord.Guild, channel_id: int):
    """TextChannel か Thread を返す。Thread は guild.get_thread で補完。"""
    ch = guild.get_channel(channel_id)
    if ch is None and hasattr(guild, "get_thread"):
        ch = guild.get_thread(channel_id)
    return ch

def is_textlike_channel(ch: Any) -> bool:
    return isinstance(ch, (discord.TextChannel, discord.Thread))


# 固定チーム順
PRESET_TEAMS = [
    ([1, 2, 7, 8], [3, 4, 5, 6]),  # 18
    ([1, 3, 5, 8], [2, 4, 6, 7]),  # 17/19
    ([1, 3, 6, 7], [2, 4, 5, 8]),  # 17/19
    ([1, 4, 5, 7], [2, 3, 6, 8]),  # 17/19
    ([1, 4, 6, 8], [2, 3, 5, 7])   # 17/19
]

def get_preset_teams(players: List[Any], game_num: int) -> Dict[str, List[Any]]:
    index_map = {i+1: players[i] for i in range(len(players))}
    team_a_nums, team_b_nums = PRESET_TEAMS[game_num - 1]
    team_a = [index_map[n] for n in team_a_nums]
    team_b = [index_map[n] for n in team_b_nums]
    return {"A": team_a, "B": team_b}

def build_overwrites_for_team(guild: discord.Guild, members: List[discord.Member]) -> Dict[Any, discord.PermissionOverwrite]:
    overwrites: Dict[Any, discord.PermissionOverwrite] = {}
    overwrites[guild.default_role] = discord.PermissionOverwrite(view_channel=False)
    if guild.me:
        overwrites[guild.me] = discord.PermissionOverwrite(view_channel=True, send_messages=True, read_message_history=True)
    for m in members:
        if isinstance(m, discord.Member):
            overwrites[m] = discord.PermissionOverwrite(view_channel=True, send_messages=True, read_message_history=True)
    return overwrites

async def create_text_channel_safe(guild: discord.Guild, name: str, category: discord.CategoryChannel,
                                   overwrites: Dict[Any, discord.PermissionOverwrite] = None) -> discord.TextChannel | None:
    try:
        ch = await guild.create_text_channel(name=name, category=category, overwrites=overwrites)
        return ch
    except discord.errors.Forbidden:
        print("Missing Permissions: チャンネル作成権限が不足しています（Manage Channels など）。")
        return None

def real_members_only(guild: discord.Guild, players: List[Any]) -> List[discord.Member]:
    reals: List[discord.Member] = []
    for p in players:
        if isinstance(p, discord.Member):
            reals.append(p)
        elif isinstance(p, int):
            m = guild.get_member(p)
            if m:
                reals.append(m)
    return reals

def serialize_players(players: List[Any]) -> str:
    arr = []
    for p in players:
        if isinstance(p, DummyMember):
            arr.append({"t": "d", "id": abs(p.id)})
        elif isinstance(p, discord.Member):
            arr.append({"t": "r", "id": p.id})
        elif isinstance(p, int):
            arr.append({"t": "d" if p < 0 else "r", "id": abs(p)})
    return json.dumps(arr, ensure_ascii=False)

def deserialize_players(players_json: str) -> List[Any]:
    res: List[Any] = []
    if not players_json:
        return res
    try:
        arr = json.loads(players_json)
        for o in arr:
            if isinstance(o, dict) and o.get("t") == "d":
                res.append(DummyMember(int(o.get("id", 1))))
            elif isinstance(o, dict) and o.get("t") == "r":
                res.append(int(o.get("id", 0)))
    except Exception:
        pass
    return res

# ========= TrueSkill 用 DB ヘルパ =========
def ensure_user_row(user_id: int):
    cur.execute("SELECT mu, sigma FROM users WHERE user_id=?", (user_id,))
    row = cur.fetchone()
    if row is None:
        cur.execute("INSERT INTO users (user_id, mu, sigma) VALUES (?,?,?)",
                    (user_id, DEFAULT_MU, DEFAULT_SIGMA))
        conn.commit()
        user_data[user_id] = int(round(DEFAULT_MU))
        return
    mu, sigma = row
    if mu is None or sigma is None:
        mu = DEFAULT_MU if mu is None else mu
        sigma = DEFAULT_SIGMA if sigma is None else sigma
        cur.execute("UPDATE users SET mu=?, sigma=? WHERE user_id=?", (mu, sigma, user_id))
        conn.commit()
    user_data[user_id] = int(round(mu if mu is not None else DEFAULT_MU))

def get_user_trueskill(user_id: int) -> trueskill.Rating:
    ensure_user_row(user_id)
    cur.execute("SELECT mu, sigma FROM users WHERE user_id=?", (user_id,))
    mu, sigma = cur.fetchone()
    return ts.Rating(mu=mu, sigma=sigma)

def set_user_trueskill(user_id: int, rating: trueskill.Rating):
    cur.execute("UPDATE users SET mu=?, sigma=? WHERE user_id=?", (rating.mu, rating.sigma, user_id))
    conn.commit()
    user_data[user_id] = int(round(rating.mu))

def to_display(mu: float) -> float:
    return round(mu * 40 + 1100, 1)


# ========= DB 保存/読込 =========
def save_waiting_players():
    cur.execute("DELETE FROM waiting_players")
    if waiting_players:
        cur.executemany("INSERT INTO waiting_players (id) VALUES (?)", [(p,) for p in waiting_players])
    conn.commit()

def save_in_match_players():
    cur.execute("DELETE FROM in_match_players")
    if in_match_players:
        cur.executemany("INSERT INTO in_match_players (id) VALUES (?)", [(p,) for p in in_match_players])
    conn.commit()

def save_match(match_id: int):
    if match_id not in current_matches:
        return
    m = current_matches[match_id]
    cur.execute("""INSERT OR REPLACE INTO matches 
        (match_id, guild_id, category_id, lobby_id, players, current_game, votes, is_dummy) 
        VALUES (?,?,?,?,?,?,?,?)""",
        (match_id, m["guild_id"], m["category_id"], m["lobby_id"],
         serialize_players(m["players"]),
         m["current_game"], json.dumps(list(m["votes"]), ensure_ascii=False), int(m["is_dummy"])))
    cur.execute("DELETE FROM games WHERE match_id=?", (match_id,))
    for g in m["games"]:
        cur.execute("""INSERT INTO games (match_id, game_num, team_a, team_b, ch_a_id, ch_b_id)
                       VALUES (?,?,?,?,?,?)""",
                    (match_id, g["game_num"], json.dumps(g["team_a"], ensure_ascii=False),
                     json.dumps(g["team_b"], ensure_ascii=False), g["ch_a_id"], g["ch_b_id"]))
    conn.commit()

def delete_match(match_id: int):
    cur.execute("DELETE FROM matches WHERE match_id=?", (match_id,))
    cur.execute("DELETE FROM games WHERE match_id=?", (match_id,))
    conn.commit()

def load_from_db():
    # mu を user_data 表示用に読み込む
    cur.execute("SELECT user_id, mu FROM users")
    for uid, mu in cur.fetchall():
        user_data[uid] = int(round(mu if mu is not None else DEFAULT_MU))
    cur.execute("SELECT id FROM waiting_players")
    waiting_players.extend([row[0] for row in cur.fetchall()])
    cur.execute("SELECT id FROM in_match_players")
    in_match_players.update([row[0] for row in cur.fetchall()])
    cur.execute("SELECT match_id, guild_id, category_id, lobby_id, players, current_game, votes, is_dummy FROM matches")
    for (match_id, guild_id, category_id, lobby_id, players_json, current_game, votes_json, is_dummy) in cur.fetchall():
        mi = {
            "guild_id": guild_id,
            "category_id": category_id,
            "players": deserialize_players(players_json),
            "lobby_id": lobby_id,
            "games": [],
            "current_game": current_game,
            "votes": set(json.loads(votes_json) if votes_json else []),
            "is_dummy": bool(is_dummy)
        }
        cur.execute("SELECT game_num, team_a, team_b, ch_a_id, ch_b_id FROM games WHERE match_id=? ORDER BY game_num ASC", (match_id,))
        for gnum, ta, tb, ca, cb in cur.fetchall():
            mi["games"].append({
                "game_num": gnum,
                "team_a": json.loads(ta) if ta else [],
                "team_b": json.loads(tb) if tb else [],
                "ch_a_id": ca,
                "ch_b_id": cb
            })
        current_matches[match_id] = mi

def build_result_message(guild: discord.Guild, mi: dict, aborted: bool = False) -> discord.Embed:
    """最終結果の順位表をEmbedで組み立てる"""
    all_players = set()
    for g in mi["games"]:
        all_players.update(g["team_a"])
        all_players.update(g["team_b"])
    win_count = {uid: 0 for uid in all_players}

    for g in mi["games"]:
        team_a = set(g["team_a"])
        team_b = set(g["team_b"])
        votes = g.get("vote_results", {})
        a_score = sum(1 for uid, v in votes.items() if uid in team_a and v == "win")
        b_score = sum(1 for uid, v in votes.items() if uid in team_b and v == "win")
        if a_score > b_score:
            for uid in team_a:
                win_count[uid] += 1
        elif b_score > a_score:
            for uid in team_b:
                win_count[uid] += 1

    def name_of(uid: int) -> str:
        if uid < 0:
            return f"Dummy{abs(uid)}"
        m = guild.get_member(uid)
        if m:
            return m.display_name            # キャッシュにいればOK
        return f"<@{uid}>"              # キャッシュになくてもメンション扱い


    ranking = sorted(win_count.items(), key=lambda x: x[1], reverse=True)

    embed = discord.Embed(
        title="🏆 結果（勝利数順） 🏆",
        color=discord.Color.gold()
    )

    for i, (uid, wins) in enumerate(ranking, start=1):
        old_mu = mi["start_ratings"].get(uid, DEFAULT_MU)
        new_rating = get_user_trueskill(uid)

        old_disp = to_display(old_mu)
        new_disp = to_display(new_rating.mu)

        diff = new_disp - old_disp
        arrow = "🔹" if diff >= 0 else "🔸"

        embed.add_field(
            name=f"{name_of(uid)}　{wins}勝",
            value=f"{old_disp:.1f} → {new_disp:.1f} ({arrow}{diff:+.1f})",
            inline=False
        )

    if aborted:
        embed.set_footer(text="⚠️ このマッチは中止されました。")

    return embed




# ========= 新: レート順マッチング関数 =========
async def try_match_players_by_rating(guild: discord.Guild):
    global waiting_players
    if len(waiting_players) < PLAYERS_NEEDED:
        return
    players_with_rating = []
    for uid in waiting_players:
        ensure_user_row(uid)
        r = get_user_trueskill(uid)
        players_with_rating.append((uid, r.mu))
    players_with_rating.sort(key=lambda x: x[1], reverse=True)
    while len(players_with_rating) >= PLAYERS_NEEDED:
        group_ids = [uid for uid, _ in players_with_rating[:PLAYERS_NEEDED]]
        players_with_rating = players_with_rating[PLAYERS_NEEDED:]
        waiting_players = [uid for uid in waiting_players if uid not in group_ids]
        save_waiting_players()
        group_members = [guild.get_member(uid) for uid in group_ids]
        await start_match_core(guild, group_members, is_dummy_mode=False)

# ==== 共通処理を関数に分離 ====
async def handle_match_join(interaction: discord.Interaction):
    guild = interaction.guild or bot.get_guild(GUILD_ID)
    if not guild:
        await interaction.response.send_message("⚠️ サーバーが見つかりません。", ephemeral=True)
        return

    member = guild.get_member(interaction.user.id)
    if not member:
        await interaction.response.send_message("⚠️ サーバーに参加していません。", ephemeral=True)
        return

    user_id = member.id
    ensure_user_row(user_id)
    if user_id in in_match_players:
        await interaction.response.send_message("現在進行中のマッチに参加中です。", ephemeral=True)
        return
    if user_id in waiting_players:
        await interaction.response.send_message("すでに待機リストに入っています。", ephemeral=True)
        return
    for match in current_matches.values():
        if user_id in [p if isinstance(p, int) else (p.id if isinstance(p, discord.Member) else None) for p in match["players"]]:
            await interaction.response.send_message("現在進行中のマッチに参加中です。", ephemeral=True)
            return

    waiting_players.append(user_id)
    save_waiting_players()
    await interaction.response.send_message(f"待機リストに参加しました",ephemeral=True)


async def handle_match_leave(interaction: discord.Interaction):
    guild = interaction.guild or bot.get_guild(GUILD_ID)
    if not guild:
        await interaction.response.send_message("⚠️ サーバーが見つかりません。", ephemeral=True)
        return

    member = guild.get_member(interaction.user.id)
    if not member:
        await interaction.response.send_message("⚠️ サーバーに参加していません。", ephemeral=True)
        return

    user_id = member.id
    if user_id not in waiting_players:
        await interaction.response.send_message("待機リストに入っていません。", ephemeral=True)
        return

    waiting_players.remove(user_id)
    save_waiting_players()
    await interaction.response.send_message(
        f"待機リストから退出しました。",
        ephemeral=True
    )

# ========= 定期チェックタスク =========
@tasks.loop(seconds=MATCHMAKING_INTERVAL)
async def matchmaking_loop():
    for guild in bot.guilds:
        await try_match_players_by_rating(guild)

@bot.event
async def on_member_join(member: discord.Member):
    guild = member.guild
    # category = guild.get_channel(1407518929026416831)  # 専用カテゴリ
    
    ensure_user_row(member.id)

   

# @bot.tree.command(name="r", description="指定ユーザー、または自分のレートを確認します")
# async def str_command(interaction: discord.Interaction, target: str | None = None):
#     guild = interaction.guild or bot.get_guild(GUILD_ID)
#     if not guild:
#         await interaction.response.send_message("⚠️ サーバーが見つかりません。", ephemeral=True)
#         return

#     result = find_member_by_input(guild, target, interaction.user)

#     if isinstance(result, list):  # 複数候補
#         candidates = "\n".join([f"- {m.display_name} (ID: {m.name})" for m in result[:10]])
#         await interaction.response.send_message(
#             f"⚠️ 名前 `{target}` に一致するユーザーが複数います。\n以下から選んでください：\n{candidates}",
#             ephemeral=True
#         )
#         return

#     member = result
#     if not member:
#         await interaction.response.send_message(f"⚠️ ユーザー `{target}` が見つかりません。", ephemeral=True)
#         return
#     if member.bot:
#         await interaction.response.send_message("Botは指定できません。", ephemeral=True)
#         return

#     # TrueSkill 取得
#     r = get_user_trueskill(member.id)
#     display = to_display(r.mu)

#     # 順位計算
#     cur.execute("SELECT user_id, mu FROM users")
#     all_users = cur.fetchall()
#     sorted_users = sorted(all_users, key=lambda x: x[1], reverse=True)
#     rank = next((i for i, (uid, _) in enumerate(sorted_users, start=1) if uid == member.id), None)
#     total = len(sorted_users)

#     msg = f"{member.display_name} | {display:.1f} | "
#     if rank:
#         msg += f"{rank}位 / {total}人中"

#     await interaction.response.send_message(msg, ephemeral=True)




# @bot.tree.command(name="w", description="自分や指定ユーザーの勝率を表示します")
# async def winrate_command(interaction: discord.Interaction, target: str | None = None):
#     guild = interaction.guild or bot.get_guild(GUILD_ID)
#     if not guild:
#         await interaction.response.send_message("⚠️ サーバーが見つかりません。", ephemeral=True)
#         return

#     result = find_member_by_input(guild, target, interaction.user)

#     if isinstance(result, list):  # 複数候補
#         candidates = "\n".join([f"- {m.display_name} (ID: {m.name})" for m in result[:10]])
#         await interaction.response.send_message(
#             f"⚠️ 名前 `{target}` に一致するユーザーが複数います。\n以下から選んでください：\n{candidates}",
#             ephemeral=True
#         )
#         return

#     member = result
#     if not member:
#         await interaction.response.send_message(f"⚠️ ユーザー `{target}` が見つかりません。", ephemeral=True)
#         return
#     if member.bot:
#         await interaction.response.send_message("Botは指定できません。", ephemeral=True)
#         return

#     ensure_user_row(member.id)
#     cur.execute("SELECT wins, games FROM users WHERE user_id=?", (member.id,))
#     wins, games = cur.fetchone()
#     if not games or games == 0:
#         msg = f"{member.display_name} さんはまだ試合データがありません。"
#     else:
#         wr = wins / games * 100
#         msg = f"{member.display_name} さんの勝率: {wins}/{games} ({wr:.1f}%)"

#     await interaction.response.send_message(msg, ephemeral=True)

import discord

@bot.tree.command(name="s", description="指定ユーザー、または自分の成績を確認します")
async def status_command(interaction: discord.Interaction, target: str | None = None):
    guild = interaction.guild or bot.get_guild(GUILD_ID)
    if not guild:
        await interaction.response.send_message("⚠️ サーバーが見つかりません。", ephemeral=True)
        return

    result = find_member_by_input(guild, target, interaction.user)

    if isinstance(result, list):  # 複数候補
        candidates = "\n".join([f"- {m.display_name} (ID: {m.name})" for m in result[:10]])
        await interaction.response.send_message(
            f"⚠️ 名前 `{target}` に一致するユーザーが複数います。\n以下から選んでください：\n{candidates}",
            ephemeral=True
        )
        return

    member = result
    if not member:
        await interaction.response.send_message(f"⚠️ ユーザー `{target}` が見つかりません。", ephemeral=True)
        return
    if member.bot:
        await interaction.response.send_message("Botは指定できません。", ephemeral=True)
        return

    # TrueSkill 取得
    r = get_user_trueskill(member.id)
    display = to_display(r.mu)

    # 順位計算
    cur.execute("SELECT user_id, mu FROM users")
    all_users = cur.fetchall()
    sorted_users = sorted(all_users, key=lambda x: x[1], reverse=True)
    rank = next((i for i, (uid, _) in enumerate(sorted_users, start=1) if uid == member.id), None)
    total = len(sorted_users)

    # 勝率計算
    ensure_user_row(member.id)
    cur.execute("SELECT wins, games FROM users WHERE user_id=?", (member.id,))
    wins, games = cur.fetchone()
    if not games or games == 0:
        wr_text = "試合データなし"
    else:
        wr = wins / games * 100
        wr_text = f"{wr:.1f}% ({wins}/{games})"

    # Embed 組み立て
    embed = discord.Embed(
        title=f"{member.display_name}",
        color=discord.Color.blue()
    )
    embed.add_field(name="レート", value=f"{display:.1f}", inline=True)
    if rank:
        embed.add_field(name="順位", value=f"{rank}位 / {total}人中", inline=True)
    embed.add_field(name="勝率", value=wr_text, inline=True)

    await interaction.response.send_message(embed=embed, ephemeral=True)

class RankingView(View):
    def __init__(self, pages: list[discord.Embed], user: discord.User,
                 start: int, end: int, guild: discord.Guild):
        super().__init__(timeout=None)  # ⬅ 無期限
        self.pages = pages
        self.current = 0
        self.user = user
        self.start = start
        self.end = end
        self.guild = guild
        self.update_buttons()

    def update_buttons(self):
        for child in self.children:
            if isinstance(child, Button):
                if child.custom_id == "first":
                    child.disabled = self.current == 0
                elif child.custom_id == "prev":
                    child.disabled = self.current == 0
                elif child.custom_id == "next":
                    child.disabled = self.current == len(self.pages) - 1
                elif child.custom_id == "last":
                    child.disabled = self.current == len(self.pages) - 1

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        # 実行者以外は操作不可
        if interaction.user.id != self.user.id:
            await interaction.response.send_message("⚠️ この操作はコマンド実行者のみ可能です。", ephemeral=True)
            return False
        return True

    @discord.ui.button(label="⏮", style=discord.ButtonStyle.secondary, custom_id="first")
    async def first_page(self, interaction: discord.Interaction, button: Button):
        self.current = 0
        self.update_buttons()
        await interaction.response.edit_message(embed=self.pages[self.current], view=self)

    @discord.ui.button(label="◀", style=discord.ButtonStyle.secondary, custom_id="prev")
    async def prev_page(self, interaction: discord.Interaction, button: Button):
        self.current -= 1
        self.update_buttons()
        await interaction.response.edit_message(embed=self.pages[self.current], view=self)

    @discord.ui.button(label="▶", style=discord.ButtonStyle.secondary, custom_id="next")
    async def next_page(self, interaction: discord.Interaction, button: Button):
        self.current += 1
        self.update_buttons()
        await interaction.response.edit_message(embed=self.pages[self.current], view=self)

    @discord.ui.button(label="⏭", style=discord.ButtonStyle.secondary, custom_id="last")
    async def last_page(self, interaction: discord.Interaction, button: Button):
        self.current = len(self.pages) - 1
        self.update_buttons()
        await interaction.response.edit_message(embed=self.pages[self.current], view=self)

    @discord.ui.button(label="🔄 更新", style=discord.ButtonStyle.primary, custom_id="refresh")
    async def refresh(self, interaction: discord.Interaction, button: Button):
        # DBから再取得して最新の順位表を作り直す
        cur.execute("SELECT user_id, mu FROM users")
        all_users = cur.fetchall()
        sorted_users = sorted(all_users, key=lambda x: x[1], reverse=True)

        total = len(sorted_users)
        start = max(1, self.start)
        end = min(total, self.end)

        lines = []
        for i in range(start, end + 1):
            uid, mu = sorted_users[i - 1]
            member = self.guild.get_member(uid)
            name = member.display_name if member else f"Unknown({uid})"
            lines.append(f"{i}位: {name} | {mu:.1f}")

        PAGE_SIZE = 20
        self.pages = []
        for i in range(0, len(lines), PAGE_SIZE):
            chunk = lines[i:i + PAGE_SIZE]
            embed = discord.Embed(
                title=f"レート順位表 {start}位〜{end}位",
                description="\n".join(chunk),
                color=discord.Color.gold()
            )
            embed.set_footer(text=f"ページ {len(self.pages)+1}/{(len(lines)-1)//PAGE_SIZE+1}")
            self.pages.append(embed)

        # ページ番号をリセットして再表示
        self.current = 0
        self.update_buttons()
        await interaction.response.edit_message(embed=self.pages[self.current], view=self)


@bot.tree.command(name="r", description="レートの順位表を表示します")
async def ranking_command(
    interaction: discord.Interaction,
    start: int | None = None,
    end: int | None = None
):
    # 範囲決定
    if start is None and end is None:
        start, end = 1, 100
    elif start is not None and end is None:
        start, end = 1, start
    else:
        if start is None or end is None:
            await interaction.response.send_message("⚠️ 引数の指定が不正です。", ephemeral=True)
            return
        if start > end:
            start, end = end, start

    # DB から全ユーザー取得
    cur.execute("SELECT user_id, mu FROM users")
    all_users = cur.fetchall()
    if not all_users:
        await interaction.response.send_message("⚠️ ユーザーデータがありません。", ephemeral=True)
        return

    # ソート
    sorted_users = sorted(all_users, key=lambda x: x[1], reverse=True)
    total = len(sorted_users)

    start = max(1, start)
    end = min(total, end)
    if start > total:
        await interaction.response.send_message("⚠️ 指定範囲にユーザーがいません。", ephemeral=True)
        return

    # ライン作成
    lines = []
    for i in range(start, end + 1):
        uid, mu = sorted_users[i - 1]
        member = interaction.guild.get_member(uid)
        name = member.display_name if member else f"Unknown({uid})"
        lines.append(f"{i}位: {name} | {mu:.1f}")

    PAGE_SIZE = 20
    pages = []
    for i in range(0, len(lines), PAGE_SIZE):
        chunk = lines[i:i + PAGE_SIZE]
        embed = discord.Embed(
            title=f"順位表 {start}位〜{end}位",
            description="\n".join(chunk),
            color=discord.Color.gold()
        )
        embed.set_footer(text=f"ページ {len(pages)+1}/{(len(lines)-1)//PAGE_SIZE+1}")
        pages.append(embed)

    view = RankingView(pages, interaction.user, start, end, interaction.guild)
    await interaction.response.send_message(embed=pages[0], view=view, ephemeral=True)

@bot.tree.command(name="c", description="マッチング待機リストに参加")
async def match_join(interaction: discord.Interaction):
    await handle_match_join(interaction)


@bot.tree.command(name="match_random8", description="管理者用：サーバー内からランダムに8人選んでマッチ開始（テスト用）")
async def match_random8(interaction: discord.Interaction):
    guild = interaction.guild or bot.get_guild(GUILD_ID)
    if not guild:
        await interaction.response.send_message("⚠️ サーバーが見つかりません。", ephemeral=True)
        return

    member = guild.get_member(interaction.user.id)
    if not member or not member.guild_permissions.administrator:
        await interaction.response.send_message("このコマンドは管理者のみ使用できます。", ephemeral=True)
        return

    members = [m for m in guild.members if not m.bot]
    if len(members) < PLAYERS_NEEDED:
        await interaction.response.send_message(f"メンバーが不足しています（必要: {PLAYERS_NEEDED}人）", ephemeral=True)
        return

    selected = random.sample(members, PLAYERS_NEEDED)
    for m in selected:
        ensure_user_row(m.id)

    await interaction.response.send_message("ランダム8人でマッチを開始します。", ephemeral=True)
    await start_match_core(guild, selected, is_dummy_mode=False)


@bot.tree.command(name="l", description="マッチング待機リストから抜けます")
async def match_leave(interaction: discord.Interaction):
    await handle_match_leave(interaction)

# ========= マッチ進行関連の関数 =========
async def start_match_core(guild: discord.Guild, players: List[Any], is_dummy_mode: bool):
    parent_category = guild.get_channel(PARENT_CHANNEL_ID)
    if not isinstance(parent_category, discord.CategoryChannel):
        print(f"カテゴリが見つからないか、IDがカテゴリではありません: {PARENT_CHANNEL_ID}")
        return

    # match_idの採番
    match_id = random.randint(1000, 9999)
    while match_id in current_matches:
        match_id = random.randint(1000, 9999)

    # 権限設定
    overwrites = {guild.default_role: discord.PermissionOverwrite(read_messages=False)}
    real_players = real_members_only(guild, players)
    for m in real_players:
        overwrites[m] = discord.PermissionOverwrite(read_messages=True, send_messages=True)

    # ロビー作成
    lobby = await guild.create_text_channel(
        name=f"ロビー{match_id}",
        category=parent_category,
        overwrites=overwrites
    )

    mentions, mus = [], []
    for p in players:
        if isinstance(p, DummyMember):
            mentions.append(p.mention+"\n")
        elif isinstance(p, discord.Member):
            mentions.append(p.mention+"\n")
            mus.append(get_user_trueskill(p.id).mu)
        elif isinstance(p, int):
            m = guild.get_member(p)
            if m:
                mentions.append(m.mention+"\n")
                mus.append(get_user_trueskill(p).mu)

    await lobby.send(f"**マッチングしました！** \n参加者:\n👑{' '.join(mentions)}")
    if mus:
        avg_mu = sum(mus) / len(mus)
        await lobby.send(f"📊 このマッチの平均レート: **{to_display(avg_mu):.1f}**")

    # === ホスト決定（待機リスト先頭 = players[0]） ===
    host_member = None
    first_player = players[0]
    if isinstance(first_player, discord.Member):
        host_member = first_player
    elif isinstance(first_player, int):
        host_member = guild.get_member(first_player)

    if host_member:
        await lobby.send(
            f"ホストは {host_member.mention} さんです！\n"
            f"下のボタンからヘヤタテURLを入力してください。"
        )
        # ホスト専用ボタンを追加
        host_view = HostLinkView(host_member, lobby)
        bot.add_view(host_view)
        await lobby.send(view=host_view)

    # マッチ情報を保存
    current_matches[match_id] = {
        "guild_id": guild.id,
        "category_id": parent_category.id,
        "players": players,
        "lobby_id": lobby.id,
        "games": [],
        "current_game": 1,
        "votes": set(),
        "is_dummy": is_dummy_mode
    }

    for m in real_players:
        in_match_players.add(m.id)
        ensure_user_row(m.id)
    save_in_match_players()

    cancel_view = CancelMatchView(match_id)
    bot.add_view(cancel_view)
    await lobby.send("⚠️ 対戦を中止する場合はこちら（5票で成立）", view=cancel_view)

    report_view = ReportButtonView(match_id)
    bot.add_view(report_view)
    await lobby.send("🚨 プレイヤーを通報する場合はこちら", view=report_view)

    await create_and_announce_game(guild, match_id, game_num=1)
    await send_vote_buttons(guild, match_id, game_num=1, lobby_id=lobby.id)
    save_match(match_id)



async def create_and_announce_game(guild: discord.Guild, match_id: int, game_num: int):
    mi = current_matches.get(match_id)
    if not mi:
        return

    lobby = guild.get_channel(mi["lobby_id"])
    if not isinstance(lobby, discord.TextChannel):
        return

    def id_of(p):
        if isinstance(p, DummyMember):
            return p.id
        elif isinstance(p, discord.Member):
            return p.id
        elif isinstance(p, int):
            return p
        return None

    teams = get_preset_teams(mi["players"], game_num)
    team_a_list, team_b_list = teams["A"], teams["B"]

    team_a_members = real_members_only(guild, team_a_list)
    team_b_members = real_members_only(guild, team_b_list)

    def mentions_for(lst):
        res = []
        for p in lst:
            if isinstance(p, DummyMember):
                res.append(p.mention)
            elif isinstance(p, discord.Member):
                res.append(p.mention)
            elif isinstance(p, int):
                m = guild.get_member(p)
                res.append(m.mention if m else str(p))
        return " ".join(res)

    # ✅ 先にチーム分けメッセージを送る
    await lobby.send(
        f"**試合 {game_num} 開始！**\n"
        f"チームA: {mentions_for(team_a_list)}\n"
        f"チームB: {mentions_for(team_b_list)}\n"
    )

    # その後でチームスレッドを作成
    ch_a = await lobby.create_thread(
        name=f"試合{game_num}-チームA",
        type=discord.ChannelType.private_thread
    )
    ch_b = await lobby.create_thread(
        name=f"試合{game_num}-チームB",
        type=discord.ChannelType.private_thread
    )

    # チームAに招待
    for m in team_a_members:
        try:
            await ch_a.add_user(m)
            await asyncio.sleep(0.5)  # API連打回避
        except Exception as e:
            print(f"チームA追加失敗: {m} {e}")

    # チームBに招待
    for m in team_b_members:
        try:
            await ch_b.add_user(m)
            await asyncio.sleep(0.5)
        except Exception as e:
            print(f"チームB追加失敗: {m} {e}")

    # DB用に保存
    mi["teams"] = {"A": [id_of(p) for p in team_a_list], "B": [id_of(p) for p in team_b_list]}
    mi["games"].append({
        "game_num": game_num,
        "team_a": mi["teams"]["A"],
        "team_b": mi["teams"]["B"],
        "ch_a_id": ch_a.id,
        "ch_b_id": ch_b.id
    })

    save_match(match_id)




async def cleanup_game_threads(guild: discord.Guild, match_id: int, game_num: int):
    mi = current_matches.get(match_id)
    if not mi:
        return
    for g in mi.get("games", []):
        if g["game_num"] == game_num:
            for key in ("ch_a_id", "ch_b_id"):
                th = get_textlike(guild, g.get(key))
                if isinstance(th, discord.Thread):
                    try:
                        await th.delete()
                    except discord.Forbidden:
                        pass



async def send_vote_buttons(guild: discord.Guild, match_id: int, game_num: int, lobby_id: int):
    lobby = get_textlike(guild, lobby_id)
    if not is_textlike_channel(lobby):
        return
    view = ResultButtonView(match_id=match_id, game_num=game_num)
    bot.add_view(view)  # Persistent View
    await lobby.send(f"**試合 {game_num} の結果を登録してください**（8人中{VOTE_THRESHOLD}票で次へ）", view=view)

async def end_match(guild: discord.Guild, match_id: int):
    mi = current_matches.get(match_id)
    if not mi:
        return

    # ロビー削除（配下のチームスレッドも自動削除される）
    lobby = guild.get_channel(mi.get("lobby_id"))
    if isinstance(lobby, discord.TextChannel):
        try:
            await lobby.delete()
        except discord.Forbidden:
            pass

    # 参加解除
    for m in real_members_only(guild, mi["players"]):
        in_match_players.discard(m.id)
    save_in_match_players()

    current_matches.pop(match_id, None)
    delete_match(match_id)
    print(f"マッチ {match_id} を終了しました。")




# ========= TrueSkill レート更新ロジック =========
def _collect_real_ids(ids: List[int]) -> List[int]:
    return [uid for uid in ids if isinstance(uid, int) and uid > 0]

async def apply_trueskill_updates(
    guild: discord.Guild,
    lobby_id: int,
    team_a_ids: List[int],
    team_b_ids: List[int],
    outcome: str,
    start_mus: Dict[int, float]
):
    ratings_a = [get_user_trueskill(uid) for uid in team_a_ids]
    ratings_b = [get_user_trueskill(uid) for uid in team_b_ids]

    if outcome == "A":
        new_a, new_b = ts.rate([ratings_a, ratings_b], ranks=[0, 1])
    elif outcome == "B":
        new_a, new_b = ts.rate([ratings_a, ratings_b], ranks=[1, 0])
    else:
        new_a, new_b = ts.rate([ratings_a, ratings_b], ranks=[0, 0])

    for uid, r in zip(team_a_ids, new_a):
        set_user_trueskill(uid, r)
    for uid, r in zip(team_b_ids, new_b):
        set_user_trueskill(uid, r)

    lobby = get_textlike(guild, lobby_id)
    if is_textlike_channel(lobby):
        # （必要ならここで結果一覧を lobby.send できます）
        pass

    # DB更新（既存処理のまま）
    for uid in team_a_ids + team_b_ids:
        cur.execute("UPDATE users SET games = COALESCE(games, 0) + 1 WHERE user_id=?", (uid,))
    if outcome == "A":
        for uid in team_a_ids:
            cur.execute("UPDATE users SET wins = COALESCE(wins, 0) + 1 WHERE user_id=?", (uid,))
    elif outcome == "B":
        for uid in team_b_ids:
            cur.execute("UPDATE users SET wins = COALESCE(wins, 0) + 1 WHERE user_id=?", (uid,))
    conn.commit()


# ========= ボタン View =========
class ResultButtonView(discord.ui.View):
    """Persistent View対応：custom_id を固定化して再起動後も有効に"""
    def __init__(self, match_id: int, game_num: int):
        super().__init__(timeout=None)
        self.match_id = match_id
        self.game_num = game_num

        self.add_item(discord.ui.Button(label="勝ち", style=discord.ButtonStyle.green,
                                        custom_id=self._custom_id("win")))
        self.add_item(discord.ui.Button(label="負け", style=discord.ButtonStyle.red,
                                        custom_id=self._custom_id("lose")))

    def _custom_id(self, kind: str) -> str:
        return f"match:{self.match_id}:game:{self.game_num}:{kind}"

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        cid = interaction.data.get("custom_id", "")
        if cid.endswith(":win"):
            await self._handle_vote(interaction, "win")
            return False
        elif cid.endswith(":lose"):
            await self._handle_vote(interaction, "lose")
            return False
        return False

    async def _handle_vote(self, interaction: discord.Interaction, result: str):
        mi = current_matches.get(self.match_id)
        if not mi:
            await interaction.response.send_message("このマッチは存在しません。", ephemeral=True)
            return

        if mi["current_game"] != self.game_num:
            await interaction.response.send_message("この試合の投票は締め切られました。", ephemeral=True)
            return

        valid_ids = {
            p.id if isinstance(p, discord.Member) else p
            for p in mi["players"]
            if not isinstance(p, DummyMember) and (isinstance(p, discord.Member) or isinstance(p, int))
        }
        valid_ids = {pid for pid in valid_ids if pid > 0}

        if interaction.user.id not in valid_ids:
            await interaction.response.send_message("このマッチの参加者のみ投票できます。", ephemeral=True)
            return

        if "vote_results" not in mi:
            mi["vote_results"] = {}

        if interaction.user.id in mi["vote_results"]:
            await interaction.response.send_message("この試合にはすでに投票済みです。", ephemeral=True)
            return

        mi["vote_results"][interaction.user.id] = result.lower()
        await interaction.response.send_message(
            f"投票を受け付けました（{len(mi['vote_results'])}/{VOTE_THRESHOLD}）", ephemeral=True
        )
        save_match(self.match_id)

        if len(mi["vote_results"]) >= VOTE_THRESHOLD:
            winner = self._determine_winner(mi)
            game_index = self.game_num - 1
            mi["games"][game_index]["vote_results"] = dict(mi["vote_results"])

            guild = interaction.guild
            lobby = get_textlike(guild, mi["lobby_id"])

            if winner == "retry":
                mi["vote_results"].clear()
                save_match(self.match_id)
                if is_textlike_channel(lobby):
                    await lobby.send(f"⚠️ 投票結果が不一致です。試合 {self.game_num} を再投票します。")
                return

            if is_textlike_channel(lobby):
                await lobby.send(f"**試合 {self.game_num} の結果: チーム {winner} 勝利！**")

            team_b_ids = _collect_real_ids(mi["teams"]["B"])
            team_a_ids = _collect_real_ids(mi["teams"]["A"])
            if "start_ratings" not in mi:
                start_ratings = {}
                for uid in set(team_a_ids + team_b_ids):
                    start_ratings[uid] = get_user_trueskill(uid).mu
                mi["start_ratings"] = start_ratings

            await apply_trueskill_updates(
                guild,
                mi["lobby_id"],
                team_a_ids,
                team_b_ids,
                "A" if winner == "A" else ("B" if winner == "B" else "draw"),
                mi["start_ratings"]
            )

            # ← ここで直前のチームスレッドを掃除
            await cleanup_game_threads(guild, self.match_id, self.game_num)

            if mi["current_game"] < TOTAL_GAMES:
                mi["current_game"] += 1
                mi["vote_results"].clear()
                await create_and_announce_game(guild, self.match_id, game_num=mi["current_game"])
                await send_vote_buttons(guild, self.match_id, game_num=mi["current_game"], lobby_id=mi["lobby_id"])
                save_match(self.match_id)
            else:
                final_text = build_result_message(guild, mi, aborted=False)

                if is_textlike_channel(lobby):
                    await lobby.send(embed=final_text)
                    await lobby.send("**全試合終了！お疲れさまでした！**")

                for uid in [u for u in mi["start_ratings"].keys() if u > 0]:
                    member = guild.get_member(uid)
                    if member and not member.bot:
                        try:
                            await member.send(embed=final_text)
                        except discord.Forbidden:
                            pass

                await end_match(guild, self.match_id)



    def _determine_winner(self, mi):
        votes = mi["vote_results"]
        team_a = set(mi["teams"]["A"])
        team_b = set(mi["teams"]["B"])

        # 投票が存在しない場合 → 再投票
        if not votes:
            return "retry"

        # チームごとの投票内容を収集
        a_votes = [v for uid, v in votes.items() if uid in team_a]
        b_votes = [v for uid, v in votes.items() if uid in team_b]

        # どちらかのチームが投票していない → 再投票
        if not a_votes or not b_votes:
            return "retry"

        # チーム内で割れている場合 → 再投票
        if len(set(a_votes)) > 1 or len(set(b_votes)) > 1:
            return "retry"

        # 全員勝ち or 全員負け → 再投票
        if all(v == "win" for v in a_votes + b_votes):
            return "retry"
        if all(v == "lose" for v in a_votes + b_votes):
            return "retry"

        # 得点方式（勝ちなら+1、負けなら-1）
        a_score = sum(1 if v == "win" else -1 for v in a_votes)
        b_score = sum(1 if v == "win" else -1 for v in b_votes)

        if a_score > b_score:
            return "A"
        elif b_score > a_score:
            return "B"
        else:
            return "retry"  # 引き分けになったら再投票

class CancelMatchView(discord.ui.View):
    def __init__(self, match_id: int):
        super().__init__(timeout=None)
        self.match_id = match_id
        self.add_item(discord.ui.Button(label="⚠️ 対戦中止", style=discord.ButtonStyle.danger,
                                        custom_id=f"match:{match_id}:cancel"))

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        mi = current_matches.get(self.match_id)
        if not mi:
            await interaction.response.send_message("このマッチは存在しません。", ephemeral=True)
            return False

        if "cancel_votes" not in mi:
            mi["cancel_votes"] = set()

        if interaction.user.id in mi["cancel_votes"]:
            await interaction.response.send_message("すでに中止に投票済みです。", ephemeral=True)
            return False

        mi["cancel_votes"].add(interaction.user.id)
        await interaction.response.send_message(
            f"対戦中止に投票しました ({len(mi['cancel_votes'])}/{VOTE_THRESHOLD})", ephemeral=True
        )

        if len(mi["cancel_votes"]) >= VOTE_THRESHOLD:
            guild = interaction.guild
            lobby = get_textlike(guild, mi["lobby_id"])
            if is_textlike_channel(lobby):
                await lobby.send("⚠️ **対戦が中止されました**")

            if "start_ratings" in mi:
                final_text = build_result_message(guild, mi, aborted=True)
                if is_textlike_channel(lobby):
                    await lobby.send(embed=final_text)
                for uid in [u for u in mi["start_ratings"].keys() if u > 0]:
                    member = guild.get_member(uid)
                    if member and not member.bot:
                        try:
                            await member.send(embed=final_text)
                        except discord.Forbidden:
                            pass

            await end_match(guild, self.match_id)

        return False



class ReportReasonSelect(discord.ui.Select):
    def __init__(self, reporter: discord.Member, target: discord.Member, match_id: int):
        self.reporter = reporter
        self.target = target
        self.match_id = match_id
        options = [
            discord.SelectOption(label="部屋に合流しない", value="部屋に合流しない"),
            discord.SelectOption(label="故意の通信切断", value="故意の通信切断"),
            discord.SelectOption(label="利敵・妨害行為", value="利敵・妨害行為"),
            discord.SelectOption(label="不適切な発言", value="不適切な発言"),
        ]
        super().__init__(placeholder="通報理由を選択してください", options=options, min_values=1, max_values=1)

    async def callback(self, interaction: discord.Interaction):
        reason = self.values[0]
        cur.execute(
            "INSERT INTO reports (reporter_id, target_id, reason, match_id) VALUES (?,?,?,?)",
            (self.reporter.id, self.target.id, reason, self.match_id)
        )
        conn.commit()

        await interaction.response.send_message(
            f"✅ {self.target.mention} を通報しました（理由: {reason}）", ephemeral=True
        )
        # mog-logチャンネルへ送信
        guild = interaction.guild
        log_ch = discord.utils.get(guild.text_channels, name="mog-log")
        if log_ch:
            reporter_name = self.reporter.display_name
            target_name = self.target.display_name
            await log_ch.send(
                f"🚨 **通報ログ**\n"
                f"試合ID: {self.match_id}\n"
                f"通報者: {reporter_name} ({self.reporter.id})\n"
                f"対象: {target_name} ({self.target.id})\n"
                f"理由: {reason}"
            )
class HostLinkModal(discord.ui.Modal, title="ヘヤタテURL入力"):
    link = discord.ui.TextInput(
        label="ヘヤタテURL",
        style=discord.TextStyle.short,
        
    )

    def __init__(self, host: discord.Member, lobby_channel: discord.TextChannel):
        super().__init__()
        self.host = host
        self.lobby_channel = lobby_channel

    async def on_submit(self, interaction: discord.Interaction):
        await self.lobby_channel.send(
            f"🔗 {self.host.mention} さんが共有したヘヤタテURL: **{self.link.value}**"
        )
        await interaction.response.send_message("✅ URLを登録しました！", ephemeral=True)


class HostLinkView(discord.ui.View):
    def __init__(self, host: discord.Member, lobby_channel: discord.TextChannel):
        super().__init__(timeout=None)
        self.host = host
        self.lobby_channel = lobby_channel

    @discord.ui.button(label="URLを入力する", style=discord.ButtonStyle.primary, custom_id="host_link")
    async def host_link_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.host.id:
            await interaction.response.send_message("⚠️ あなたはホストではありません。", ephemeral=True)
            return
        await interaction.response.send_modal(HostLinkModal(self.host, self.lobby_channel))

class ReportButtonView(discord.ui.View):
    def __init__(self, match_id: int):
        super().__init__(timeout=None)
        self.match_id = match_id
        self.add_item(discord.ui.Button(label="🚨 通報", style=discord.ButtonStyle.secondary,
                                        custom_id=f"match:{match_id}:report"))

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        mi = current_matches.get(self.match_id)
        if not mi:
            await interaction.response.send_message("このマッチは存在しません。", ephemeral=True)
            return False

        # 対象プレイヤー一覧
        options = []
        for p in mi["players"]:
            uid = p.id if isinstance(p, discord.Member) else (p if isinstance(p, int) else None)
            if uid and uid > 0:
                m = interaction.guild.get_member(uid)
                if m:
                    options.append(discord.SelectOption(label=m.display_name, value=str(m.id)))

        if not options:
            await interaction.response.send_message("通報可能なプレイヤーが見つかりません。", ephemeral=True)
            return False

        # ドロップダウンで対象を選ばせる
        select = discord.ui.Select(placeholder="通報対象を選んでください", options=options, min_values=1, max_values=1)

        async def select_callback(inter: discord.Interaction):
            target_id = int(select.values[0])
            target = inter.guild.get_member(target_id)
            if not target:
                await inter.response.send_message("対象が見つかりません。", ephemeral=True)
                return
            view = discord.ui.View(timeout=60)
            view.add_item(ReportReasonSelect(inter.user, target, self.match_id))
            await inter.response.send_message(
                f"{target.mention} を通報します。理由を選んでください：", view=view, ephemeral=True
            )

        select.callback = select_callback
        view = discord.ui.View(timeout=30)
        view.add_item(select)
        await interaction.response.send_message("通報対象を選んでください：", view=view, ephemeral=True)
        return False

# === ボタン定義（Persistent対応） ===
class MatchControlView(discord.ui.View):
    def __init__(self):
        super().__init__(timeout=None)

    @discord.ui.button(
        label="エントリー",
        style=discord.ButtonStyle.primary,
        custom_id="match_join"
    )
    async def join_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        await handle_match_join(interaction)

    @discord.ui.button(
        label="取り消し",
        style=discord.ButtonStyle.danger,
        custom_id="match_leave"
    )
    async def leave_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        await handle_match_leave(interaction)




# ========= 起動時復元 & 定期マッチング開始 =========
@bot.event
async def on_guild_join(guild: discord.Guild):
    # 初回起動時だけメッセージを送る（必要なら）
    channel = bot.get_channel(1407578550944399490)
    if channel:
        sent = await channel.send("マッチング操作はこちらから！", view=MatchControlView())
        await sent.pin()  # ← ここでピン留め
        print("✅ ボタンメッセージを送信しました")

@bot.event
async def on_ready():
    print(f"Botログイン: {bot.user}")
    bot.add_view(MatchControlView())

    
    load_from_db()
    for match_id, mi in current_matches.items():
        try:
            view = ResultButtonView(match_id=match_id, game_num=mi["current_game"])
            bot.add_view(view)
            bot.add_view(CancelMatchView(match_id))
            bot.add_view(ReportButtonView(match_id))
        except Exception as e:
            print(f"PersistentView再登録失敗 match_id={match_id}: {e}")
    try:
        synced = await bot.tree.sync()
        print(f"/コマンド同期: {len(synced)} 個")
    except Exception as e:
        print(f"同期エラー: {e}")
        
    if not matchmaking_loop.is_running():
        matchmaking_loop.start()

# ========= 実行 =========
if __name__ == "__main__":
    if not TOKEN or TOKEN == "YOUR_DISCORD_TOKEN_HERE":
        raise SystemExit("環境変数 DISCORD_TOKEN を設定してください。")
    bot.run(TOKEN)
