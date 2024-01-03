use std::collections::BinaryHeap;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::{Debug, Formatter, Result};
use std::hash::Hash;
use std::io;

type Action = (isize, isize);
type State = Vec<Vec<usize>>;
const ACTIONS: [Action; 4] = [(1, 0), (0, -1), (-1, 0), (0, 1)];

pub struct SegTree<X: Clone> {
    n: usize,
    fx: fn(X, X) -> X,
    ex: X,
    pub dat: Vec<X>,
}

impl<X: Clone> SegTree<X> {
    pub fn new(n_: usize, fx: fn(X, X) -> X, ex: X) -> Self {
        let mut x = 1;
        while n_ > x {
            x *= 2;
        }
        let n = x;
        let dat = vec![ex.clone(); n * 4];
        SegTree { n, fx, ex, dat }
    }

    pub fn set(&mut self, i: usize, v: X) {
        self.dat[i + self.n - 1] = v;
    }

    pub fn build(&mut self) {
        for k in (0..(self.n - 1)).rev() {
            self.dat[k] = (self.fx)(self.dat[2 * k + 1].clone(), self.dat[2 * k + 2].clone());
        }
    }

    pub fn update(&mut self, i: usize, v: X) {
        let mut i = i + self.n - 1;
        self.dat[i] = v;
        while i > 0 {
            i = (i - 1) / 2;
            self.dat[i] = (self.fx)(self.dat[2 * i + 1].clone(), self.dat[2 * i + 2].clone());
        }
    }

    fn query_sub(&self, a: usize, b: usize, k: usize, l: usize, r: usize) -> X {
        if r <= a || b <= l {
            self.ex.clone()
        } else if a <= l && r <= b {
            self.dat[k].clone()
        } else {
            let vl = self.query_sub(a, b, 2 * k + 1, l, (l + r) / 2);
            let vr = self.query_sub(a, b, 2 * k + 2, (l + r) / 2, r);
            (self.fx)(vl, vr)
        }
    }

    pub fn query(&self, a: usize, b: usize) -> X {
        self.query_sub(a, b, 0, 0, self.n)
    }
}

#[derive(Clone, Eq, PartialEq, Hash)]
struct Puzzle {
    n: usize,
    m: usize,
    board: State,
    space_pos: (usize, usize),
    count: usize,
    heuristic: usize,
}

impl Puzzle {
    fn new(n: usize, m: usize, board: State) -> Self {
        let mut space_pos = (0, 0);
        for (i, row) in board.iter().enumerate() {
            for (j, col) in row.iter().enumerate() {
                if *col == 0 {
                    space_pos = (j, i);
                }
            }
        }
        Self {
            n,
            m,
            board,
            space_pos,
            count: 0,
            heuristic: 0,
        }
    }

    fn step(&mut self, action: Action) -> bool {
        let (x, y) = self.space_pos;
        let (dx, dy) = action;
        let (nx, ny) = (x as isize + dx, y as isize + dy);
        if nx < 0 || nx >= self.n as isize || ny < 0 || ny >= self.m as isize {
            return false;
        }
        let (nx, ny) = (nx as usize, ny as usize);

        let v = self.board[ny][nx];
        self.heuristic += (x as isize - (v - 1) as isize % self.m as isize).unsigned_abs()
            + (y as isize - (v - 1) as isize / self.m as isize).unsigned_abs();
        self.heuristic -= (nx as isize - (v - 1) as isize % self.m as isize).unsigned_abs();
        self.heuristic -= (ny as isize - (v - 1) as isize / self.m as isize).unsigned_abs();

        self.board[y][x] = self.board[ny][nx];
        self.board[ny][nx] = 0;
        self.space_pos = (nx, ny);
        self.count += 1;
        true
    }

    fn move_only(&mut self, action: Action) -> bool {
        let (x, y) = self.space_pos;
        let (dx, dy) = action;
        let (nx, ny) = (x as isize + dx, y as isize + dy);
        if nx < 0 || nx >= self.n as isize || ny < 0 || ny >= self.m as isize {
            return false;
        }
        let (nx, ny) = (nx as usize, ny as usize);

        self.board[y][x] = self.board[ny][nx];
        self.board[ny][nx] = 0;
        self.space_pos = (nx, ny);
        true
    }

    fn get_state(&self) -> &State {
        &self.board
    }

    fn get_legal_actions(&self) -> Vec<Action> {
        let mut actions = Vec::new();
        for action in ACTIONS.iter() {
            let (x, y) = self.space_pos;
            let (dx, dy) = *action;
            let (nx, ny) = (x as isize + dx, y as isize + dy);
            if nx < 0 || nx >= self.n as isize || ny < 0 || ny >= self.m as isize {
                continue;
            }
            actions.push(*action);
        }
        actions
    }
}

impl Debug for Puzzle {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        for i in 0..self.n {
            for j in 0..self.m {
                if j < self.m - 1 {
                    write!(f, "{} ", self.board[i][j])?;
                } else {
                    write!(f, "{}", self.board[i][j])?;
                }
            }
            writeln!(f)?;
        }
        Ok(())
    }
}

impl PartialOrd for Puzzle {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(
            (self.count + self.heuristic)
                .cmp(&(other.count + other.heuristic))
                .reverse(),
        )
    }
}

impl Ord for Puzzle {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (self.count + self.heuristic)
            .cmp(&(other.count + other.heuristic))
            .reverse()
    }
}

fn get_reverse_action(action: Action) -> Action {
    let (dx, dy) = action;
    (-dx, -dy)
}

fn is_valid(puzzle: &Puzzle) -> bool {
    let (n, m) = (puzzle.n, puzzle.m);
    let mut a = vec![false; n * m];
    let mut zero_found = false;
    for i in 0..n {
        for j in 0..m {
            let v = puzzle.board[i][j];
            if v == 0 {
                if zero_found {
                    return false;
                }
                zero_found = true;
                continue;
            }
            if v > n * m {
                return false;
            }
            if a[v - 1] {
                return false;
            }
            a[v - 1] = true;
        }
    }
    true
}

fn get_inversion_number(puzzle: &Puzzle) -> usize {
    let mut inv = 0;
    let n_ = puzzle.n * puzzle.m;
    let mut a = Vec::new();
    for i in 0..puzzle.m {
        for j in 0..puzzle.n {
            if puzzle.board[i][j] == 0 {
                a.push(puzzle.n * puzzle.m);
            } else {
                a.push(puzzle.board[i][j]);
            }
        }
    }
    let mut seg_tree = SegTree::new(n_, |x, y| x + y, 0);
    for ai in a.iter() {
        let v = ai - 1;
        inv += v - seg_tree.query(0, v);
        seg_tree.update(v, 1);
    }
    inv
}

fn is_solvable(puzzle: &Puzzle) -> bool {
    let inv = get_inversion_number(puzzle);
    let (x, y) = puzzle.space_pos;
    let (dx, dy) = (puzzle.m - 1 - x, puzzle.n - 1 - y);
    let space_manhattan_distance = dx + dy;
    inv % 2 == space_manhattan_distance % 2
}

fn create_goal(puzzle: &Puzzle) -> State {
    let (n, m) = (puzzle.n, puzzle.m);
    let mut goal = vec![];
    for i in 0..n {
        let mut line = vec![];
        for j in 0..m {
            line.push(i * m + j + 1);
        }
        goal.push(line);
    }
    goal[n - 1][m - 1] = 0;
    goal
}

#[allow(dead_code)]
fn bfs(puzzle: &Puzzle) -> Option<Vec<Action>> {
    let mut queue = VecDeque::new();
    let mut visited = HashSet::new();
    let mut parent = HashMap::new();
    queue.push_back(puzzle.get_state().clone());
    visited.insert(puzzle.get_state().clone());
    let goal = create_goal(puzzle);
    let mut visited_count = 0;
    while let Some(state) = queue.pop_front() {
        visited_count += 1;
        if visited_count % 10000 == 0 {
            eprint!("\r{}", visited_count);
        }
        let mut puzzle = Puzzle::new(puzzle.n, puzzle.m, state.clone());
        if *puzzle.get_state() == goal {
            let mut path = Vec::new();
            let mut state = puzzle.get_state();
            while let Some(action) = parent.get(state) {
                let reverse_action = get_reverse_action(*action);
                path.push(*action);
                puzzle.step(reverse_action);
                state = puzzle.get_state();
            }
            path.reverse();
            println!("visited count: {}", visited_count);
            return Some(path);
        }
        for action in puzzle.get_legal_actions() {
            let mut next_puzzle = puzzle.clone();
            next_puzzle.step(action);
            let state = next_puzzle.get_state();
            if visited.contains(state) {
                continue;
            }
            queue.push_back(state.clone());
            visited.insert(state.clone());
            parent.insert(state.clone(), action);
        }
    }
    None
}

fn get_manhattan_distance(puzzle: &Puzzle) -> usize {
    let mut distance = 0;
    for i in 0..puzzle.n {
        for j in 0..puzzle.m {
            let v = puzzle.board[i][j];
            if v == 0 {
                continue;
            }
            let (x, y) = ((v - 1) % puzzle.m, (v - 1) / puzzle.m);
            distance +=
                (x as isize - j as isize).unsigned_abs() + (y as isize - i as isize).unsigned_abs();
        }
    }
    distance
}

fn get_before_states(puzzle: &Puzzle) -> Vec<(Action, State)> {
    let mut before_states = Vec::new();
    let actions = puzzle.get_legal_actions();
    for action in actions {
        let mut puzzle = puzzle.clone();
        puzzle.move_only(action);
        let reverse_action = get_reverse_action(action);
        before_states.push((reverse_action, puzzle.get_state().clone()));
    }
    before_states
}

#[allow(dead_code)]
fn astar(puzzle: &Puzzle) -> Option<Vec<Action>> {
    let mut puzzle = puzzle.clone();
    let start = puzzle.get_state().clone();
    let mut queue = BinaryHeap::new();
    let mut visited = HashMap::new();
    let goal = create_goal(&puzzle);
    let mut count_map = HashMap::new();
    count_map.insert(start.clone(), 0);
    puzzle.heuristic = get_manhattan_distance(&puzzle);
    queue.push(puzzle);
    let mut visited_count = 0;
    while let Some(mut puzzle) = queue.pop() {
        visited_count += 1;
        if visited_count % 10000 == 0 {
            eprint!("\r{}", visited_count);
        }
        if *puzzle.get_state() == goal {
            let mut path = Vec::new();
            while *puzzle.get_state() != start {
                let before_states = get_before_states(&puzzle);
                let mut min_count = std::usize::MAX;
                let mut min_state = Vec::new();
                let mut min_action = None;
                for (action, state) in before_states.iter() {
                    if let Some(count) = count_map.get(state) {
                        if *count < min_count {
                            min_count = *count;
                            min_state = state.clone();
                            min_action = Some(*action);
                        }
                    }
                }
                puzzle = Puzzle::new(puzzle.n, puzzle.m, min_state);
                puzzle.count = min_count;
                path.push(min_action.unwrap());
            }
            path.reverse();
            println!("visited count: {}", visited_count);
            return Some(path);
        }
        visited.insert(puzzle.board.clone(), puzzle.clone());
        for action in puzzle.get_legal_actions() {
            let mut next_puzzle = puzzle.clone();
            next_puzzle.step(action);
            let state = next_puzzle.get_state();
            if count_map.contains_key(state) {
                continue;
            } else {
                count_map.insert(state.clone(), next_puzzle.count);
            }
            if let Some(puzzle) = visited.get(state) {
                if *puzzle <= next_puzzle {
                    continue;
                }
            }
            queue.push(next_puzzle);
        }
    }
    None
}

fn main() {
    let mut n_m_input = String::new();
    io::stdin()
        .read_line(&mut n_m_input)
        .expect("Failed to read line");
    let (n, m) = {
        let mut iter = n_m_input.split_whitespace();
        if iter.clone().count() != 2 {
            eprintln!("invalid");
            return;
        }
        let n: usize = iter.next().unwrap().parse().unwrap();
        let m: usize = iter.next().unwrap().parse().unwrap();
        (n, m)
    };
    let mut board = Vec::new();
    for _ in 0..n {
        let mut line = String::new();
        io::stdin().read_line(&mut line).expect("invalid");
        let mut iter = line.split_whitespace();
        if iter.clone().count() != m {
            eprintln!("invalid");
            return;
        }
        let mut row = Vec::new();
        for _ in 0..m {
            let v: usize = iter.next().unwrap().parse().unwrap();
            row.push(v);
        }
        board.push(row);
    }

    let mut puzzle = Puzzle::new(n, m, board);
    println!("{:?}", puzzle);
    if !is_valid(&puzzle) {
        eprintln!("invalid");
        return;
    }
    if !is_solvable(&puzzle) {
        println!("unsolvable");
        return;
    }
    if let Some(path) = astar(&puzzle) {
        println!("path length: {}", path.len());
        for action in path {
            println!("{} {}", action.0, action.1);
            puzzle.move_only(action);
            println!("{:?}", puzzle);
        }
    }
}
