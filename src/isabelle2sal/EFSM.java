package isabelle2sal;

import static isabelle2sal.Parser.*;
import static isabelle2sal.Generator.*;
import java.util.*;

/**
 * Deals with an EFSM; reading it in from Isabelle and converting it to a 
 * module in sal
 * @author sdn
 */
public class EFSM {
    
    //::::::::::::::::::::::::::: The Internal Representation
    
    private static Map<String,Integer> aliasesForStateNumbers = new HashMap<>();
    static void includeAlias(String alias, int state) {
       aliasesForStateNumbers.put(alias, state);
    }

    private static class Move {  //from one state to another
                        
        //::::::::::::::::::::::: The Internal Representation
    
        private int origin, destination;
        private Transition transition;
        
        private Move (int start, int finish, Transition t)  {
            origin = start;
            destination = finish;
            transition = t;
        }
        
        //::::::::::::::::::::::: Creation from Isobelle Source code
    
        private static int acceptStateNumber() throws IsabelleException, FileException {
            nextTokenMustBeOneOf(Token.NUMBER, Token.ALIAS_NAME);
            if  (  nextTokenIs(Token.ALIAS_NAME)  )
                return aliasesForStateNumbers.get(Parser.acceptedWord());
            else 
                return (int)acceptedNumber();
        }

        private static Move readOneIn() throws IsabelleException, FileException {
            accept(Token.OPENING_ROUND_BRACKET);
                accept(Token.OPENING_ROUND_BRACKET);
                    int from = acceptStateNumber();
                    accept(Token.COMMA);
                    int destination = acceptStateNumber();
                accept(Token.CLOSING_ROUND_BRACKET, Token.COMMA);
                Transition t = Transition.identifiedByName();
            accept(Token.CLOSING_ROUND_BRACKET);
            
            return new Move(from, destination, t);

        } 
                       
        //::::::::::::::::::::::: Translating from isablle to sal

        void translate(SAL sal, Transition t)  {
            t.addMove(sal.stateTest(origin), sal.stateTest(destination));
        }

    }
    
    static List<EFSM> allOfThem = new ArrayList<>(); 
    static EFSM[] theEFSMs() {
        return allOfThem.toArray(new EFSM[0]);        
    }
    static EFSM theOneCalled(String s)  {
        for (EFSM e : allOfThem)
            if  (  e.identifier.equals(s)  )  return e;
        assert false : s;
        return null;        
    }
    
    static List<Integer> allStates() {
        Set<Integer> asSet = new HashSet<>();
        for (EFSM e : allOfThem) asSet.addAll(e.theStates);
        List<Integer> asList = new ArrayList<>(asSet);
        Collections.sort(asList);
        return Collections.unmodifiableList(asList);
    }
    
    static void clearAll()  {  
        allOfThem.clear();  
    }        
    
    private Set<Integer> theStates;
    boolean hasState(Integer s)  {  return theStates.contains(s);  }
    
    private List<Transition> translatedTransitions = new ArrayList<>();  //includes duplicates
    
    private List<Move> theMoves;
    private void addMove(Move m) {
        theMoves.add(m);
        theStates.add(m.destination);
        theStates.add(m.origin);
    }
    
    private String identifier = null;    
    String getIdentifier() {  return identifier;  }
    
    private EFSM (String i) {  
        identifier = i; 
        theMoves = new ArrayList<>();
        theStates = new HashSet<>();
    }
   
    //::::::::::::::::::::::::::: Creation from Isobelle Source code
    
    static void readInNewOne(String name) throws IsabelleException, FileException {
        EFSM newOne = new EFSM(name);
        addToDictionary(name, Token.EFSM_NAME);
        allOfThem.add(newOne);  

        accept(Token.OPENING_CURLY_BRACKET);
            accept(Token.BAR);
                newOne.theMoves = new ArrayList<>();
                do {
                    newOne.addMove(Move.readOneIn());
                    nextTokenMustBeOneOf(Token.COMMA, Token.BAR);
                } while (  acceptedTokenWas(Token.COMMA));     
           accept(Token.BAR);         
        accept(Token.CLOSING_CURLY_BRACKET);         
    }
        
    //::::::::::::::::::::::::::: Translating from isablle to sal

    public void translateInto(SAL sal) throws IsabelleException, FileException {

        if  (  allOfThem.size() == 1 )
            translatedTransitions.addAll(Transition.allOfThem());
        else 
            translatedTransitions.addAll(Transition.copyOfAll());

        int extras = 0;

        for (int t =0; t<Transition.allOfThem().size(); t++)  {

            List <Move> movesOfT = new ArrayList<>();
            for (Move m : theMoves) 
                if (  Transition.allOfThem().indexOf(m.transition) == t  )  
                    movesOfT.add(m);

             if  (  movesOfT.isEmpty()  )  {
                 translatedTransitions.remove(t+extras);
                 extras--;
             }
             else if  (  movesOfT.size() == 1  )  
                movesOfT.get(0).translate(sal, translatedTransitions.get(t+extras));

            else {
                List<Transition> clones = 
                        Transition.allOfThem().get(t).
                                createVersions(sal, movesOfT.size());
                translatedTransitions.remove(t+extras);
                for (int i=0; i<movesOfT.size(); i++) {
                    translatedTransitions.add(t+extras+i, clones.get(i));
                    movesOfT.get(i).translate(sal, clones.get(i));
                }
                extras+=clones.size()-1;
            }
        }

        translatedTransitions.add(
            Transition.newNullTransition(sal.stateTest()));                   

    }

    //::::::::::::::::::::::::::: Output as SAL
    
    private void outputIntialization() throws IsabelleException, FileException  {

        outputSALLine(
                Token.INITIALIZATION, 
                Token.OPENING_SQUARE_BRACKET);

        increaseMarginOnSALOutput();

            increaseMarginOnSALOutput();

                Variable.initializeVariablesInSAL();

                outputNewLineInSAL();

            decreaseMarginOnSALOutput();

            outputSALLine(Token.GUARDED_BY);

        decreaseMarginOnSALOutput();

        outputSALLine(Token.CLOSING_SQUARE_BRACKET);

        decreaseMarginOnSALOutput();
    }
    
    public void outputModule() throws IsabelleException, FileException  {
        outputSALLine(getIdentifier(), 
                Token.COLON, 
                Token.MODULE, 
                Token.EQUALS);

        increaseMarginOnSALOutput();

            outputSALLine(Token.BEGIN);

            increaseMarginOnSALOutput();

                Variable.declareVariablesInSAL();

                outputIntialization();

                increaseMarginOnSALOutput();

                    outputSALLine(
                            Token.TRANSITION, 
                            Token.OPENING_SQUARE_BRACKET);

                    increaseMarginOnSALOutput();

                    for (Transition t : translatedTransitions)  {
                        if  (  translatedTransitions.indexOf(t) > 0  )  //not the first
                            outputSALLine(
                                Token.OPENING_SQUARE_BRACKET, 
                                Token.CLOSING_SQUARE_BRACKET);                                              
                        t.outputDefinitionAsSAL();
                    }

                decreaseMarginOnSALOutput();

                outputSALLine(Token.CLOSING_SQUARE_BRACKET);

            decreaseMarginOnSALOutput();

            outputSALLine(
                Token.END, 
                Token.SEMICOLON);
        decreaseMarginOnSALOutput();

    }
    
    //::::::::::::::::::::::::::: Output as Dot
    
    public List<Transition> dotTransitions() {
        return Collections.unmodifiableList(translatedTransitions.subList(0,
                        translatedTransitions.size()-1)); //not the last one
    }

}
