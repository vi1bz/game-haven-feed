#!/usr/bin/env python3
"""Builds games.json for Game Haven by discovering games automatically.

Reads Roblox's public Charts data, filters it with the rules in settings.json,
and writes games.json. Uses only Python's standard library and needs no keys.

If anything goes wrong the script exits with an error and leaves the existing
games.json untouched, so the game keeps showing the last good data.
"""

import json
import math
import os
import random
import re
import sys
import time
import urllib.error
import urllib.request
import uuid
from datetime import datetime, timedelta, timezone

SETTINGS_FILE = "settings.json"
OUTPUT_FILE = "games.json"
EXPLORE_URL = (
    "https://apis.roblox.com/explore-api/v1/get-sorts"
    "?sessionId={session}&device=computer&country=all"
)
GAMES_URL = "https://games.roblox.com/v1/games?universeIds={ids}"
VOTES_URL = "https://games.roblox.com/v1/games/votes?universeIds={ids}"
USER_AGENT = "GameHavenFeed/1.0"
BATCH_SIZE = 50
SHORTLIST_SIZE = 40
MAX_NAME = 60
MAX_DESCRIPTION = 140
MIN_VOTES_FOR_PERCENT = 20
VALID_MATURITY = ("minimal", "mild", "moderate")
EMOJI_PATTERN = re.compile("[\U00010000-\U0010ffff\u2190-\u2bff\ufe0f\u200d]")

DEFAULTS = {
    "allowedMaturity": ["minimal", "mild"],
    "rotationHours": 6,
    "trending": {"poolSize": 12, "count": 6, "minVotes": 100, "minLikePercent": 70},
    "hiddenGems": {
        "minPlaying": 150,
        "maxPlaying": 3000,
        "minVotes": 500,
        "minLikePercent": 85,
        "maxDaysSinceUpdate": 30,
        "poolSize": 20,
        "count": 6,
    },
    "communityPicks": [],
    "blockedUniverseIds": [],
}


# ---------------------------------------------------------------- settings

def is_number(value):
    return isinstance(value, (int, float)) and not isinstance(value, bool)


def load_settings():
    """Reads settings.json, fills in defaults, and checks everything."""
    with open(SETTINGS_FILE, "r", encoding="utf-8") as handle:
        user = json.load(handle)
    if not isinstance(user, dict):
        raise ValueError(f"{SETTINGS_FILE} must contain a JSON object")

    settings = json.loads(json.dumps(DEFAULTS))
    for key, value in user.items():
        if key not in settings:
            raise ValueError(f"Unknown setting '{key}' in {SETTINGS_FILE}")
        if isinstance(settings[key], dict):
            if not isinstance(value, dict):
                raise ValueError(f"'{key}' must be an object")
            for sub_key, sub_value in value.items():
                if sub_key not in settings[key]:
                    raise ValueError(f"Unknown setting '{key}.{sub_key}'")
                settings[key][sub_key] = sub_value
        else:
            settings[key] = value

    maturity = settings["allowedMaturity"]
    if (not isinstance(maturity, list) or not maturity
            or any(item not in VALID_MATURITY for item in maturity)):
        raise ValueError(f"'allowedMaturity' must be a list using only: {', '.join(VALID_MATURITY)}")

    if not is_number(settings["rotationHours"]) or settings["rotationHours"] <= 0:
        raise ValueError("'rotationHours' must be a number above zero")

    for section in ("trending", "hiddenGems"):
        for key, value in settings[section].items():
            if not is_number(value) or value < 0:
                raise ValueError(f"'{section}.{key}' must be a number, zero or more")

    picks = settings["communityPicks"]
    if not isinstance(picks, list):
        raise ValueError("'communityPicks' must be a list")
    for index, pick in enumerate(picks, start=1):
        universe_id = pick.get("universeId") if isinstance(pick, dict) else None
        if not isinstance(universe_id, int) or isinstance(universe_id, bool) or universe_id <= 0:
            raise ValueError(f"Community pick #{index} needs a positive whole-number 'universeId'")
        note = pick.get("note")
        if note is not None and not isinstance(note, str):
            raise ValueError(f"Community pick #{index}: 'note' must be text")

    blocked = settings["blockedUniverseIds"]
    if not isinstance(blocked, list) or any(not isinstance(item, int) for item in blocked):
        raise ValueError("'blockedUniverseIds' must be a list of whole numbers")

    return settings


# ----------------------------------------------------------------- network

def fetch_json(url):
    """Downloads JSON, retrying a few times with a growing pause."""
    last_error = None
    for attempt in range(1, 4):
        try:
            request = urllib.request.Request(
                url, headers={"User-Agent": USER_AGENT, "Accept": "application/json"}
            )
            with urllib.request.urlopen(request, timeout=30) as response:
                return json.loads(response.read().decode("utf-8"))
        except (urllib.error.URLError, TimeoutError, ValueError) as error:
            last_error = error
            print(f"Attempt {attempt} failed for {url.split('?')[0]}: {error}")
            time.sleep(2 ** attempt)
    raise RuntimeError(f"Could not fetch {url.split('?')[0]}: {last_error}")


def fetch_in_batches(url_template, ids):
    """Fetches data for many universe IDs, returning {universeId: item}."""
    results = {}
    for start in range(0, len(ids), BATCH_SIZE):
        batch = ids[start:start + BATCH_SIZE]
        payload = fetch_json(url_template.format(ids=",".join(str(i) for i in batch)))
        for item in payload.get("data", []):
            if isinstance(item, dict) and isinstance(item.get("id"), int):
                results[item["id"]] = item
    return results


def read_explore():
    """Returns {sortId: [raw game, ...]} from Roblox's Charts data."""
    payload = fetch_json(EXPLORE_URL.format(session=uuid.uuid4()))
    sorts = {}
    for sort in payload.get("sorts") or []:
        if (isinstance(sort, dict) and sort.get("contentType") == "Games"
                and isinstance(sort.get("games"), list)):
            sorts[sort.get("sortId")] = sort["games"]
    if "top-trending" not in sorts:
        raise RuntimeError(
            "Roblox's Charts data has no 'top-trending' list. The endpoint may have changed."
        )
    return sorts


# ----------------------------------------------------------------- helpers

def normalize(raw):
    """Turns one raw Charts entry into a clean dict, or None if unusable."""
    if not isinstance(raw, dict):
        return None
    universe_id = raw.get("universeId")
    name = raw.get("name")
    up = raw.get("totalUpVotes")
    down = raw.get("totalDownVotes")
    playing = raw.get("playerCount")
    if (not isinstance(universe_id, int) or not isinstance(name, str)
            or not all(isinstance(v, int) for v in (up, down, playing))):
        return None
    return {
        "universeId": universe_id,
        "name": name,
        "up": up,
        "down": down,
        "playing": playing,
        "maturity": raw.get("contentMaturity"),
        "sponsored": raw.get("isSponsored") is True,
    }


def like_ratio(game):
    votes = game["up"] + game["down"]
    return game["up"] / votes if votes else 0.0


def wilson_lower_bound(up, down, z=1.96):
    """A cautious like-percentage: small vote counts are trusted less."""
    n = up + down
    if n == 0:
        return 0.0
    p = up / n
    return (p + z * z / (2 * n) - z * math.sqrt((p * (1 - p) + z * z / (4 * n)) / n)) / (1 + z * z / n)


def strip_emoji(text):
    return EMOJI_PATTERN.sub("", text or "")


def clean_name(text):
    """Removes [TAGS] and emojis from a game title."""
    text = re.sub(r"\[[^\]]*\]", " ", text or "")
    text = strip_emoji(text)
    return re.sub(r"\s+", " ", text).strip(" -|:")


def shorten(text, limit):
    """Collapses whitespace and cuts text at a word boundary."""
    text = re.sub(r"\s+", " ", text or "").strip()
    if len(text) <= limit:
        return text
    cut = text[:limit].rsplit(" ", 1)[0]
    return cut.rstrip(" ,.;:-") + "..."


def parse_time(value):
    if not isinstance(value, str):
        return None
    cleaned = re.sub(r"\.\d+", "", value).replace("Z", "+00:00")
    try:
        parsed = datetime.fromisoformat(cleaned)
    except ValueError:
        return None
    return parsed if parsed.tzinfo else parsed.replace(tzinfo=timezone.utc)


def rotate(candidates, count, salt, rotation_hours):
    """Picks 'count' games. The pick stays the same within one rotation period
    and changes when the next period starts."""
    if len(candidates) <= count:
        return list(candidates)
    slot = int(time.time() // (rotation_hours * 3600))
    rng = random.Random(slot * 31 + salt)
    chosen = sorted(rng.sample(range(len(candidates)), count))
    return [candidates[i] for i in chosen]


def interleave(*lists):
    """Trending, Hidden Gem, Community Pick, Trending, ... so the first three
    games (your three displays) show one of each."""
    result = []
    for index in range(max(len(items) for items in lists)):
        for items in lists:
            if index < len(items):
                result.append(items[index])
    return result


def load_existing_games():
    try:
        with open(OUTPUT_FILE, "r", encoding="utf-8") as handle:
            return json.load(handle).get("games")
    except (OSError, ValueError, AttributeError):
        return None


# -------------------------------------------------------------------- main

def main():
    sys.stdout.reconfigure(encoding="utf-8")
    settings = load_settings()
    allowed_maturity = set(settings["allowedMaturity"])
    blocked = set(settings["blockedUniverseIds"])
    rotation_hours = settings["rotationHours"]

    sorts = read_explore()
    pool = {}
    for games in sorts.values():
        for raw in games:
            game = normalize(raw)
            if game and game["universeId"] not in pool:
                pool[game["universeId"]] = game
    print(f"Charts returned {len(pool)} distinct games in {len(sorts)} lists.")

    def allowed(game, min_votes):
        return (
            not game["sponsored"]
            and game["universeId"] not in blocked
            and game["maturity"] in allowed_maturity
            and game["up"] + game["down"] >= min_votes
        )

    # --- Trending: the top of Roblox's own Trending list.
    cfg = settings["trending"]
    trending_pool = []
    seen = set()
    for raw in sorts["top-trending"]:
        game = normalize(raw)
        if not game or game["universeId"] in seen:
            continue
        seen.add(game["universeId"])
        if allowed(game, cfg["minVotes"]) and like_ratio(game) * 100 >= cfg["minLikePercent"]:
            trending_pool.append(game)
        if len(trending_pool) >= int(cfg["poolSize"]):
            break
    trending = rotate(trending_pool, int(cfg["count"]), 1, rotation_hours)
    print(f"Trending: {len(trending_pool)} qualified, picked {len(trending)}.")

    # --- Hidden Gems: our own rule over the same pool.
    cfg = settings["hiddenGems"]
    if "top-playing-now" not in sorts:
        print("WARNING: no 'top-playing-now' list, so top games are only excluded by player count.")
    top_playing = set()
    for raw in sorts.get("top-playing-now", []):
        game = normalize(raw)
        if game:
            top_playing.add(game["universeId"])
    trending_ids = {game["universeId"] for game in trending_pool}

    candidates = [
        game for game in pool.values()
        if game["universeId"] not in trending_ids
        and game["universeId"] not in top_playing
        and allowed(game, cfg["minVotes"])
        and cfg["minPlaying"] <= game["playing"] <= cfg["maxPlaying"]
        and like_ratio(game) * 100 >= cfg["minLikePercent"]
    ]
    candidates.sort(key=lambda game: wilson_lower_bound(game["up"], game["down"]), reverse=True)
    shortlist = candidates[:SHORTLIST_SIZE]

    # --- Details for everything we might show.
    picks = settings["communityPicks"]
    pick_ids = [pick["universeId"] for pick in picks]
    wanted = []
    for universe_id in ([g["universeId"] for g in trending]
                        + [g["universeId"] for g in shortlist] + pick_ids):
        if universe_id not in wanted:
            wanted.append(universe_id)
    details = fetch_in_batches(GAMES_URL, wanted)

    cutoff = datetime.now(timezone.utc) - timedelta(days=cfg["maxDaysSinceUpdate"])
    hidden_pool = []
    for game in shortlist:
        info = details.get(game["universeId"])
        updated = parse_time(info.get("updated")) if info else None
        if updated and updated >= cutoff:
            hidden_pool.append(game)
        if len(hidden_pool) >= int(cfg["poolSize"]):
            break
    hidden = rotate(hidden_pool, int(cfg["count"]), 2, rotation_hours)
    print(f"Hidden Gems: {len(candidates)} candidates, {len(shortlist)} shortlisted, "
          f"{len(hidden_pool)} recently updated, picked {len(hidden)}.")

    # --- Votes for community picks that are not in the Charts data.
    votes = {}
    missing_votes = [uid for uid in pick_ids if uid not in pool]
    if missing_votes:
        try:
            votes = fetch_in_batches(VOTES_URL, missing_votes)
        except RuntimeError as error:
            print(f"WARNING: could not fetch votes for community picks. {error}")

    def build_entry(universe_id, category, selection, note=None):
        info = details.get(universe_id)
        if not info or not isinstance(info.get("name"), str):
            print(f"WARNING: no details for universe {universe_id}. Skipping it.")
            return None

        up = down = None
        if universe_id in pool:
            up, down = pool[universe_id]["up"], pool[universe_id]["down"]
        elif universe_id in votes:
            up, down = votes[universe_id].get("upVotes"), votes[universe_id].get("downVotes")

        creator = info.get("creator") if isinstance(info.get("creator"), dict) else {}
        raw_name = info["name"]
        entry = {
            "id": f"u{universe_id}",
            "name": shorten(clean_name(raw_name) or strip_emoji(raw_name), MAX_NAME),
            "category": category,
            "description": shorten(note or strip_emoji(info.get("description")), MAX_DESCRIPTION),
            "universeId": universe_id,
            "rootPlaceId": info.get("rootPlaceId"),
            "creatorName": creator.get("name"),
            "genre": info.get("genre_l1") or info.get("genre"),
            "playing": info.get("playing"),
            "visits": info.get("visits"),
            "favorites": info.get("favoritedCount"),
            "lastUpdated": info.get("updated"),
            "selection": selection,
            "isPlaceholder": False,
        }
        if isinstance(up, int) and isinstance(down, int) and up + down >= MIN_VOTES_FOR_PERCENT:
            entry["likePercent"] = round(up * 100 / (up + down))
        if not entry["name"]:
            return None
        return {key: value for key, value in entry.items() if value is not None}

    trending_entries = []
    for game in trending:
        entry = build_entry(game["universeId"], "Trending", "roblox-top-trending")
        if entry:
            trending_entries.append(entry)

    hidden_entries = []
    for game in hidden:
        entry = build_entry(game["universeId"], "Hidden Gems", "hidden-gems-rule")
        if entry:
            hidden_entries.append(entry)

    community_entries = []
    for pick in picks:
        entry = build_entry(pick["universeId"], "Community Picks", "community-pick", pick.get("note"))
        if entry:
            community_entries.append(entry)

    games = interleave(trending_entries, hidden_entries, community_entries)
    if not games:
        raise RuntimeError("No games could be built. Leaving games.json unchanged.")

    for entry in games:
        print(f"  [{entry['category']}] {entry['name']} - "
              f"{entry.get('playing', '?')} playing, {entry.get('likePercent', '?')}% liked")

    if games == load_existing_games():
        print("No changes since the last run.")
        return

    payload = {
        "schemaVersion": 1,
        "generatedAt": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "games": games,
    }
    temp_file = OUTPUT_FILE + ".tmp"
    with open(temp_file, "w", encoding="utf-8") as handle:
        json.dump(payload, handle, indent=2)
        handle.write("\n")
    os.replace(temp_file, OUTPUT_FILE)
    print(f"Wrote {len(games)} game(s) to {OUTPUT_FILE}.")


if __name__ == "__main__":
    try:
        main()
    except Exception as error:  # noqa: BLE001 - report any failure and keep the old file
        print(f"ERROR: {error}")
        sys.exit(1)
