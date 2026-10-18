-- Sportsape cloud mirror schema
-- Run once in the Supabase SQL editor (or via psql) to create the tables.
-- All writes come from the service-role key; RLS can stay enabled (service role bypasses it).

-- Every placed bet AND shadow/planned slip, mirrored losslessly.
create table if not exists public.sportsape_bets (
  id           text primary key,
  phone        text,
  kind         text,            -- 'placed' | 'shadow'
  placed_at    timestamptz,
  legs         int,
  stake        numeric,
  odds         numeric,
  possible_win numeric,
  markets      jsonb,
  probs        jsonb,
  game_ids     jsonb,
  status       text,
  settled_at   timestamptz,
  won_amount   numeric,
  recipe       jsonb,
  created_at   timestamptz not null default now()
);
create index if not exists idx_bets_phone on public.sportsape_bets (phone);
create index if not exists idx_bets_status on public.sportsape_bets (status);
create index if not exists idx_bets_placed on public.sportsape_bets (placed_at desc);

-- Every game observed by the engine, betted or NOT, for calibration.
create table if not exists public.sportsape_games (
  id          text primary key,
  game_id     text,
  name        text,
  home        text,
  away        text,
  kickoff     timestamptz,
  first_odds  jsonb,
  last_odds   jsonb,
  betted      boolean default false,
  status      text,             -- 'seen' | 'settled'
  result      jsonb,            -- final score / outcome once known
  updated_at  timestamptz not null default now()
);
create index if not exists idx_games_kickoff on public.sportsape_games (kickoff desc);

-- Calibration / stats snapshot (market_types, recipes, retirement, bandit).
create table if not exists public.sportsape_stats (
  id         text primary key,
  payload    jsonb,
  updated_at timestamptz not null default now()
);

-- Per-game settled results (betted or NOT) — the calibration denominator.
-- outcome is per-game where known, else slip-level attribution flagged.
create table if not exists public.sportsape_results (
  id          text primary key,
  game_id     text,
  market      text,
  outcome     text,             -- 'won' | 'lost' | 'void' | 'unknown'
  source      text,             -- 'bet' | 'shadow'
  phone       text,
  slip_status text,             -- 'won' | 'lost' — the parent slip's outcome
  settled_at  timestamptz,
  created_at  timestamptz not null default now()
);
create index if not exists idx_results_game on public.sportsape_results (game_id);
create index if not exists idx_results_market on public.sportsape_results (market);
create index if not exists idx_results_outcome on public.sportsape_results (outcome);

