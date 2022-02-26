import java.io.*;
import java.util.*;

public class SAT {
    static int L; // total number of literals
    static int C; // total number of clauses
    
    static Clause clauses[]; // an array of clauses
    
    static Stack<Integer> forced_moves = new Stack<Integer>(); // used for back propagating in pure literal and unit propagation
    
    static int[] model; // stores the final model
    static boolean[] assumed; // stores the literals which have been assumed or forced

    static void run(String filename) throws Exception{
        Scanner sc = new Scanner(new File(filename)); // used to parse the cnf
        
        while (sc.next().equals("c")) { // skip over comment lines in the cnf
            sc.nextLine();
        }

        String formula_type = sc.next(); // cnf or dnf
        int modifier = formula_type.equals("cnf") ? 1 : -1; // if dnf, convert to cnf --- the model of the cnf will be UNSAT for dnf 

        L = sc.nextInt(); // scanning literal count
        C = sc.nextInt(); // scanning clause count
        
        model = new int[L+1]; // initializing model array
        assumed = new boolean[L+1]; // initializing assumed array
        
        clauses = new Clause[C]; // initializing clauses array
        
        for(int i = 0; i < C; i++) {
            clauses[i] = new Clause();
            int cnt_literal = 0;
            do {
                cnt_literal = sc.nextInt(); 
                clauses[i].update_literal(cnt_literal*modifier); // parsing file and assigning literals
            } while (cnt_literal != 0);
        }

        if (construct(1)) { // assuming literal 1 at the very beginning
            System.out.print("[ ");
            for(int i = 1; i <= L; i++)
                System.out.print((model[i] != 0 ? model[i] : i) + " ");
            System.out.print("]");
            System.out.println();
        } else { // if initial assumption fails, then no model and hence UNSAT
            System.out.println("UNSAT");
        }
    }

    public static void main(String[] args) throws Exception{ // to run the file
        Scanner sc = new Scanner(System.in);
        System.out.println("Put the DIMACS file in the testcase folder and enter the filename: ");
        String URL = sc.next();
        double startTime = System.currentTimeMillis();
        run("testcases/"+URL);
        double endTime = System.currentTimeMillis();
        System.out.println("Evaluation took: "+(endTime-startTime)+"ms");
        sc.close();
        // for(int i = 1; i <= 20; i++) {
        //     double startTime = System.currentTimeMillis();
        //     run("testcases/uuf150-0"+i+".cnf");
        //     double endTime = System.currentTimeMillis();
        //     System.err.println("Testcase: "+i+" took "+(endTime-startTime)+"ms");
        // }
    }

    static boolean set_literal(int literal, int val) {  // to update all clauses after setting a value of a literal
        assumed[literal] = true; // literal has been assumed, hence it is set to true
        boolean violated = false; // while setting the literal, if any contradiction occurs, then we have to reset the literal

        for (int i = 0; i < C; i++) {
            if (clauses[i].not_to_be_considered || !clauses[i].contains_literals(literal)) { continue; } // if clause is tautological, or if the literal does not belong to the clause, we do not have to make any changes in it
            clauses[i].add_assumption(literal, val); // otherwise, add the appropriate assumption to the clause
            violated |= clauses[i].violated(); // if the clause gets violated after assumption, then set violated to true
        }
        
        return !violated; // return whether setting literal was successful (no violations) or not (there has been atleast one violation)
    }

    static void reset_literal(int literal, int val) { // to reset the value of the clause when there is a failure after setting
        assumed[literal] = false; // assumed is set to false since an assumption is being removed

        for (int i = 0; i < C; i++) {
            if (clauses[i].not_to_be_considered || !clauses[i].contains_literals(literal)) { continue; }
            clauses[i].remove_assumption(literal, val); // removing assumption from the clause
        }
    }

    static int unit_propagate() { // used to apply unit propagation
        int propagated = 0; // number of clauses where unit propagation were applied
        
        for (int i = 0; i < C; i++) {
            if (clauses[i].not_to_be_considered) { continue; } // skip over tautological clauses
            
            int propagate = clauses[i].unit_propagable(); // test if clause i can be unit propagated
            if (propagate == -1) continue; // if clause i is not unit propagable, skip it

            propagated++; // increase number of propagated clauses by 1
            forced_moves.push(propagate); // add assumption to a stack --- used for backtracking
            
            if (!set_literal(Math.abs(propagate), propagate > 0 ? +1 : -1)) { de_propagate(propagated); return -1; } // if setting the assumption fails, call backtracking and remove precisely 
                                                                                                                     // the number of clauses that were unit propagated in this function call
            
            i = -1; // if unit propagation was successful, restart the search to check more unit propagations
        }
        
        return propagated; // return the number of unit propagated clauses 
    }

    static int pure_literate() { // apply pure literal optimization
        int pure_literals = 0; // number of literals where pure literal optimization could be applied

        outer:
        for (int i = 1; i <= L; i++) {
            if (assumed[i]) { continue; } // if the literal is already assumed, continue
            int state = 0; // stores the polarity of the literal
            
            for (int j = 0; j < C; j++) { // run through all the clauses
                if(clauses[j].not_to_be_considered) { continue; }
                if (clauses[j].contains_literals(i) && !clauses[j].satisfied()) {
                    if (state == 0) { state = clauses[j].literals[i]; } // if polarity has not yet been assigned, assign the current clauses' polarity to the literal
                    else if (state != clauses[j].literals[i]) { continue outer; } // if the polarity does not match, then the literal is not pure, so move to the next literal
                }
            }

            if (state != 0) { // otherwise the literal is pure
                pure_literals++; // increase the count by one

                forced_moves.push(i * state); // add the assumption to the stack

                if (!set_literal(i, state)) { // if setting the assumption fails, then call backtracking
                    de_propagate(pure_literals); // backtrack precisely through the number of pure literals that were found in this iteration
                    return -1; // failure of pure literal
                }
                
                i = 0; // reset the iterator to check for pure literals again
            }
        }

        return pure_literals; // return the number of pure literals
    }

    static void de_propagate(int propagations) { // backtracking for unit propagation and pure literals
        while (propagations-- > 0) { // only backpropagate through a set number of elements
            int literal = forced_moves.pop(); // pop element
            reset_literal(Math.abs(literal), literal > 0 ? +1 : -1); // reset the assumption
        }
    }

    static void get_propagations(int propagations) { // used for adding the forced moves to the final model
        while (propagations-- > 0) {
            int literal = forced_moves.pop();
            model[Math.abs(literal)] = literal; // pop the assumption and add it to the model
        }
    }

    static int force_moves() { // combines both unit propagations and pure literals into a single function
        int total_propagations = 0; // total number of forced moves

        while(true) { // while pure literals and unit propagation is producing some change in the set of clauses, continue applying the same
            int propagations = unit_propagate();
            if (propagations == -1) { return -1; } // failure of unit propagations
            
            int pure_literals = pure_literate();
            if (pure_literals == -1) { return -1; } // failure of pure literals

            total_propagations += propagations + pure_literals; // total number of forced assumptions

            if (propagations == 0 && pure_literals == 0) { break; } // if no change in clause set, break from while
        }
        return total_propagations; // return the total number of forced assumptions
    }

    static boolean construct(int literal) { // called whenever an assumption needs to be made
        if (literal == -1) { return true; } // if literal is -1, formula is SAT
        
        if (set_literal(literal, -1)) { // first set the literal to false
            int total_propagations = force_moves(); // apply unit propagation and pure literal
            if (total_propagations != -1) { // if total propagations has not failed, then move onto the next assumption
                if (construct(next_literal())) { model[literal] = -literal; get_propagations(total_propagations); return true; }; // if the formula is SAT, update model and also include the forced assumptions in the model
                de_propagate(total_propagations); // else if the assumption fails, remove the forced moves
            }
        }
        reset_literal(literal, -1); // reset the assumption

        if (set_literal(literal, 1)) { // now set the literal to true
            int total_propagations = force_moves();
            if (total_propagations != -1) {
                if (construct(next_literal())) { model[literal] = +literal; get_propagations(total_propagations); return true; };
                de_propagate(total_propagations);
            }
        }
        reset_literal(literal, 1); // reset the literal

        return false; // both decisions failed implies this path is contradictory
    }

    static int next_literal() { // heuristic to find the next literal to assume
        int min_clause_size = Integer.MAX_VALUE; // we find the unsatisfied clause with the minimum length
        int min_clause_index = -1; // and assume one of its literals

        for (int i = 0; i < C; i++) {
            if (clauses[i].satisfied() || clauses[i].not_to_be_considered) { continue; }
            if (min_clause_size > clauses[i].literal_count) { min_clause_size = clauses[i].literal_count; min_clause_index = i; } // finding the index of the minimum clause
        }

        if (min_clause_index == -1) return -1;

        for (int j = 1; j <= L; j++) {
            if (clauses[min_clause_index].contains_literals(j) && !assumed[j]) { return j; } // finding an unassumed literal from the minimum length clause
        }

        return -1; // otherwise, all clauses have been satisfied, and hence the formula is SAT
    }

    static class Clause {
        public boolean not_to_be_considered = false; // for clauses that are discarded due to tautology in the clause iself

        public int[] literals; // stores the literals in the clause
        private int literal_count = -1; // number of unresolved literals remaining in the clause
        public int satisfactions = 0; // number of true literals under the assumptions in the clause
        
        Clause() { // initializing the literal array
            literals = new int[L+1];
        }

        public void update_literal(int literal) { // only called during scanning and constructing the clause
            int number = Math.abs(literal);
            if (literals[number] * literal < 0) { not_to_be_considered = true; } // tautology in the clause
            else { literals[number] = (literal > 0 ? 1 : -1); }
            literal_count++; // increasing the size of the clause
        }

        public int unit_propagable() { // checks whether the clause can be unit propagated
            if (!satisfied() && literal_count == 1) { // only perform unit propagation on a clause if it has not been satisfied yet and its literal count is one
                for (int i = 1; i <= L; i++) { 
                    if (contains_literals(i) && !assumed[i]) {
                        return literals[i] * i;
                    }
                }
            }
            return -1;
        }

        public boolean contains_literals(int literal) { // returns whether the clause contains a particular literal
            return literals[literal] != 0;
        }

        public boolean satisfied() { // returns whether the clause is satisfied or not
            return satisfactions > 0;
        }

        public boolean violated() { // returns whether the clause has not been satisfied under the current assumptions
            return (literal_count == 0 && !satisfied());
        }

        public void add_assumption(int literal, int assumption) { // adds an assumption to the clause and updates it accordingly
            if (literals[literal] * assumption > 0) { satisfactions++; } // if assumption satisfies a literal in the clause, then increase satisfactions by one
            if (literals[literal] != 0) { literal_count--; } // else if the assumption does not satisfy the literal, reduce unresolved literals by one
        }

        public void remove_assumption(int literal, int assumption) { // removing an assumption when the assumption fails
            if (literals[literal] * assumption > 0) { satisfactions--; } // decreasing number of satisfaction if the assumption satisfied a literal in the clause
            if (literals[literal] != 0) { literal_count++; } // increasing the number of unresolved literals since an assumption is being removed
        }
    }

    static boolean SAT_Checker() { // to check whether a model satisifies the cnf --- used for checking correctness of output
        outer:
        for (int i = 0; i < C; i++) {
            if(clauses[i].not_to_be_considered) continue;
            for (int j = 1; j <= L; j++) {
                if (clauses[i].literals[j] * model[j] > 0) {
                    continue outer;
                }
            }
            return false;
        }

        return true;
    }
}