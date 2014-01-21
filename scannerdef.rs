
use std::hashmap::{HashMap, HashSet};
use statemachine::{StateMachine, StateId, Epsilon, StateSet, ToDfaResult, Partitioning};
use regex::{Regex};

struct ScannerDefinition<TokenType> {
    prioritized_rules: ~[(Regex, TokenType)]
}

impl<TokenType: Pod+IterBytes+Eq+Clone> ScannerDefinition<TokenType> {
    pub fn to_state_machine(&self) -> (StateMachine, StateId, HashMap<StateId, TokenType>) {
        // Generate NFA from definition
        let (nfa, nfa_start_state, nfa_end_state_to_token_map) = self.to_nfa();
        let nfa_end_states = nfa_end_state_to_token_map.keys().map(|x| *x).collect::<StateSet>();

        // Generate DFA from NFA
        let ToDfaResult { dfa,
                          start_state: dfa_start_state,
                          end_state_map: dfa_end_state_map } = nfa.to_dfa(nfa_start_state,
                                                                          &nfa_end_states);
        // Find out which DFA states map to which token
        let dfa_end_state_to_token_map = {
            // Build an ordering for tokens from the order they appear in the rule set
            let token_priority = self.prioritized_rules
                                     .iter()
                                     .enumerate()
                                     .map(|(i, &(_, token))| (token, i))
                                     .collect::<HashMap<TokenType, uint>>();

            let mut dfa_end_state_to_token_map = HashMap::<StateId, TokenType>::new();

            for (&dfa_end_state, nfa_end_states) in dfa_end_state_map.iter() {
                assert!(nfa_end_states.len() >= 1);
                let token = nfa_end_states
                    .iter()
                    .map(|s_ref| nfa_end_state_to_token_map.get_copy(s_ref))
                    .min_by(|t_ref| token_priority.get_copy(t_ref))
                    .unwrap()
                    .clone();

                dfa_end_state_to_token_map.insert(dfa_end_state, token);
            }

            dfa_end_state_to_token_map
        };

        // Minimize DFA
        let initial_partitioning = {
            // Group end states by the token they signify
            let token_to_dfa_end_state_map = {
                let mut token_to_dfa_end_state_map = HashMap::new();

                for (dfa_end_state, token) in dfa_end_state_to_token_map.iter() {
                    let state_set = token_to_dfa_end_state_map.find_or_insert_with(token,
                        |_| HashSet::new());
                    state_set.insert(*dfa_end_state);
                }

                token_to_dfa_end_state_map
            };

            // Collect the rest of the state machines states
            let non_accepting_states = {
                let mut non_accepting_states = dfa.states();

                for state_set in token_to_dfa_end_state_map.values() {
                    for state_id in state_set.iter() {
                        assert!(non_accepting_states.contains(state_id));
                        non_accepting_states.remove(state_id);
                    }
                }

                non_accepting_states
            };

            Partitioning(token_to_dfa_end_state_map.values().map(|x| x.clone()).to_owned_vec() +
                         ~[non_accepting_states])
        };

        // Create minimal DFA
        let (minimal_dfa, dfa_to_minimal_dfa_state_map) = dfa.to_minimal(&initial_partitioning);

        // Map minimal DFA end states to tokens
        let minimal_dfa_end_state_to_token_map = {
            let mut minimal_dfa_end_state_to_token_map = HashMap::new();

            for dfa_end_state in dfa_end_state_map.keys() {
                let minimal_dfa_end_state = dfa_to_minimal_dfa_state_map.get_copy(dfa_end_state);
                let token = dfa_end_state_to_token_map.get_copy(dfa_end_state);
                minimal_dfa_end_state_to_token_map.insert(minimal_dfa_end_state, token);
            }

            minimal_dfa_end_state_to_token_map
        };

        let minimal_dfa_start_state = dfa_to_minimal_dfa_state_map.get_copy(&dfa_start_state);

        return (minimal_dfa, minimal_dfa_start_state, minimal_dfa_end_state_to_token_map);
    }

    fn to_nfa(&self) -> (StateMachine, StateId, HashMap<StateId, TokenType>) {
        let mut end_state_to_token = HashMap::new();
        let mut nfa = StateMachine::new();
        let nfa_start_state = nfa.add_state();

        for &(ref regex, token_type) in self.prioritized_rules.iter() {
            let (regex_sm, regex_start_state, regex_end_state) = regex.to_state_machine();
            end_state_to_token.insert(regex_end_state, token_type);
            nfa.consume(regex_sm);
            nfa.add_transition(nfa_start_state, regex_start_state, Epsilon);
        }

        (nfa, nfa_start_state, end_state_to_token)
    }
}


struct SlowScanner<TokenType> {
    dfa: StateMachine,
    start_state: StateId,
    end_state_to_token_map: HashMap<StateId, TokenType>,
}

impl<TokenType: Pod+IterBytes+Eq+Clone> SlowScanner<TokenType> {

    pub fn new(sd: &ScannerDefinition<TokenType>) -> SlowScanner<TokenType> {
        let (dfa, start, end_states) = sd.to_state_machine();
        SlowScanner {
            dfa: dfa,
            start_state: start,
            end_state_to_token_map: end_states
        }
    }

    pub fn scan(&self, input: &str) -> Option<TokenType> {
        let mut current_state = self.start_state;
        let mut state_history = ~[current_state];

        for c in input.chars() {
            match self.dfa.get_successor_state(current_state, c) {
                Some(successor_state) => {
                    current_state = successor_state;
                    state_history.push(current_state);
                }
                None => break
            };
        }

        for state_id in state_history.rev_iter() {
            match self.end_state_to_token_map.find_copy(state_id) {
                Some(token) => {
                    return Some(token);
                }
                None => { /* do nothing */ }
            }
        }

        return None;
    }
}

#[cfg(test)]
mod tests {
    use super::{ScannerDefinition, SlowScanner};
    use regex::{Leaf, Seq, Union};

    #[deriving(Eq, IterBytes, Clone)]
    enum Token {
        A,
        B,
        C,
    }

    #[test]
    pub fn test_simple() {
        let rules = ~[(Leaf('a'), A), (Leaf('b'), B), (Leaf('c'), C)];

        let sd = ScannerDefinition {
            prioritized_rules: rules
        };

        let slow_scanner = SlowScanner::new(&sd);

        assert_eq!(slow_scanner.scan("a"), Some(A));
        assert_eq!(slow_scanner.scan("b"), Some(B));
        assert_eq!(slow_scanner.scan("c"), Some(C));

        assert_eq!(slow_scanner.scan(""), None);
        assert_eq!(slow_scanner.scan("d"), None);
        assert_eq!(slow_scanner.scan("0"), None);

        assert_eq!(slow_scanner.scan("ab"), Some(A));
        assert_eq!(slow_scanner.scan("bc"), Some(B));
        assert_eq!(slow_scanner.scan("ca"), Some(C));
    }

    #[test]
    pub fn test_longest_match() {
        let rules = ~[(Leaf('a'), A),
                      (Seq(~Leaf('a'), ~Leaf('a')), B),
                      (Seq(~Leaf('a'), ~Seq(~Leaf('a'), ~Leaf('a'))), C)];

        let sd = ScannerDefinition {
            prioritized_rules: rules
        };

        let slow_scanner = SlowScanner::new(&sd);

        assert_eq!(slow_scanner.scan(""), None);
        assert_eq!(slow_scanner.scan("a"), Some(A));
        assert_eq!(slow_scanner.scan("aa"), Some(B));
        assert_eq!(slow_scanner.scan("aaa"), Some(C));
        assert_eq!(slow_scanner.scan("aaaa"), Some(C));
        assert_eq!(slow_scanner.scan("aaaaaa"), Some(C));
    }

    #[test]
    pub fn test_priority() {
        {
            let rules = ~[(Leaf('a'), A),
                          (Union(~Leaf('a'), ~Leaf('b')), B)];

            let sd = ScannerDefinition {
                prioritized_rules: rules
            };

            let slow_scanner = SlowScanner::new(&sd);

            assert_eq!(slow_scanner.scan(""), None);
            assert_eq!(slow_scanner.scan("a"), Some(A));
            assert_eq!(slow_scanner.scan("b"), Some(B));
        }

        {
            // Reversed priority
            let rules = ~[(Union(~Leaf('a'), ~Leaf('b')), B),
                          (Leaf('a'), A)];

            let sd = ScannerDefinition {
                prioritized_rules: rules
            };

            let slow_scanner = SlowScanner::new(&sd);

            assert_eq!(slow_scanner.scan(""), None);
            assert_eq!(slow_scanner.scan("a"), Some(B));
            assert_eq!(slow_scanner.scan("b"), Some(B));
        }
    }
}