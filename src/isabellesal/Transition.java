package isabellesal;

import static isabellesal.Parser.*;
import static isabellesal.Generator.*;
import java.util.*;

/**
 * Deals with transitions in both isabelle and sal
 * @author Siobhan
 */
public class Transition   {
    
    //::::::::::::::::::::::::::: The Internal Representation
    
    //This is the list of transitions in the order they were declared
    private static List <Transition> allOfThem = new ArrayList<>();  
    static List <Transition>  allOfThem() {
        return Collections.unmodifiableList(allOfThem);
    }

    //This is the index to look them up by name needed for EFSM
    private static Map<String, Transition> byName = new HashMap<>();
    static Transition identifiedByName() throws IsabelleException, FileException {
        if  (  nextTokenIs(Token.IMPORT_NAME)  )  {
            acceptToken();
            accept(Token.DOT);
        }
        nextTokenMustBe(Token.TRANSITION_NAME);
        return byName.get(acceptedWord());
    }
    
    static void clearAll()  {
        allOfThem.clear();
        byName.clear();
    }
    
    private String identifier = null;
    
    String getIdentifier() {  return identifier;  }

    void setIdentifier(String i)  { 
        identifier = i; 
    }
    
    private SystemConstant transitionLabel;
    
    private int arity;
    private List<Guard> guard;    
    private static Map <Integer, IOVariable> inputs = new HashMap<>();    
    private OutputExpression outputs;    
    private List<Assignment> updates; 
    
    private static Map <Integer, RegisterVariable>  registers = new HashMap<>();
    
    private Assignment initialStateTest;
    private Assignment initialLabelTest;
    private List<OverflowExpression> overAndUnderFlowTests;

    private Transition(String i)  {  identifier = i;   }
                   
    //::::::::::::::::::::::::::: Creation from Isobelle Source code    
    
    //Used when reading in variables
    
    void addRegister(int n, RegisterVariable r)  {
        registers.put(n, r);
    }
    
    RegisterVariable getRegister(int n) {  return registers.get(n);  }
    
    boolean hasRegister(int n) {  return registers.containsKey(n);  }
    
    public void addInput(int n, IOVariable r)  {
        inputs.put(n, r);
    }
    
    public IOVariable getInput(int n) {  return inputs.get(n);  }
    
    public boolean hasInput(int n) {  return inputs.containsKey(n);  }
    
    //Used when reading in the actual transition
    
    private void readInGuard() throws IsabelleException, FileException {
        accept(Token.GUARDS, 
                Token.EQUALS,
                Token.OPENING_SQUARE_BRACKET);
        
        if  (  nextTokenIs(Token.CLOSING_SQUARE_BRACKET)   )
            guard = null;
        else  {
            guard = new ArrayList<>();
            do  {
                guard.add(Guard.readItIn(this));  //Its a guard
                nextTokenMustBeOneOf(Token.COMMA, Token.CLOSING_SQUARE_BRACKET);
            } while (  acceptedTokenWas(Token.COMMA));
        }

        accept (
                Token.CLOSING_SQUARE_BRACKET,
                Token.COMMA); 

    }
    
    private void readInLabelAndArity() throws IsabelleException, FileException {
        accept( Token.LABEL,
                Token.EQUALS); 
        
        nextTokenMustBeOneOf(Token.OPENING_ROUND_BRACKET, Token.STR);  
        boolean needsClosingBracket = acceptedTokenWas(Token.OPENING_ROUND_BRACKET);
        accept(Token.STR);
        nextTokenMustBe(Token.STRING);
        transitionLabel = SystemConstant.fromLabel(nextWord());
        acceptToken(); 
        if  (  needsClosingBracket  )   accept(Token.CLOSING_ROUND_BRACKET);        
        accept(Token.COMMA);
        
        accept( Token.ARITY, 
                Token.EQUALS );            
        nextTokenMustBe(Token.NUMBER);
        arity = (int)acceptedNumber();
        accept(Token.COMMA);
    }
    
    private void readInOutputs() throws IsabelleException, FileException  {
        accept( Token.OUTPUTS, 
                Token.EQUALS, 
                Token.OPENING_SQUARE_BRACKET);
        

        if  (  nextTokenIs(Token.CLOSING_SQUARE_BRACKET)  )  
            outputs = null;
        else {
            outputs = new OutputExpression();        
            do  {
                outputs.add(Expression.readItIn(this));
                nextTokenMustBeOneOf(Token.COMMA, Token.CLOSING_SQUARE_BRACKET);
            }
            while  (  acceptedTokenWas(Token.COMMA)  );
        }
        accept(Token.CLOSING_SQUARE_BRACKET); 
        
        accept(Token.COMMA);
    }
    
    private void readInUpdates() throws IsabelleException, FileException {
        accept( Token.UPDATES, 
                Token.EQUALS); 
        
        updates = new ArrayList<>();            
        accept(Token.OPENING_SQUARE_BRACKET);
            boolean unfinished = ! nextTokenIs(Token.CLOSING_SQUARE_BRACKET);
            while (  unfinished  )  {
                accept(Token.OPENING_ROUND_BRACKET);
                    nextTokenMustBe(Token.NUMBER);
                    Variable lhs = RegisterVariable.numbered((int)acceptedNumber(), this); 
                    accept(Token.COMMA);
                    updates.add(
                            Assignment.newOne(
                                    lhs,
                                    Expression.readItIn(this)));
                accept(Token.CLOSING_ROUND_BRACKET);
                nextTokenMustBeOneOf(Token.COMMA, Token.CLOSING_SQUARE_BRACKET);
                unfinished = acceptedTokenWas(Token.COMMA);
            }             
        accept(Token.CLOSING_SQUARE_BRACKET); 
 
    }
    
    static void readOneIn (String i) throws IsabelleException, FileException {
        
        Transition newOne = new Transition(i);
        addToDictionary(i, Token.TRANSITION_NAME);    
        
        accept( Token.LEFT_PARR);
        
        newOne.readInLabelAndArity();    
        newOne.readInGuard();
        newOne.readInOutputs();       
        newOne.readInUpdates();

        accept( Token.RIGHT_PARR);
        
        allOfThem.add(newOne);
        byName.put(i, newOne);

    }
        
    //::::::::::::::::::::::::::: Translating from isablle to sal
    
    void addMove(Assignment before, Assignment afterwards) {
        initialStateTest = before; //It could be null for an else transition
        if  (  updates == null  )  updates = new ArrayList<>();
        updates.add(0,afterwards);
    }

    static List<Transition> copyOfAll() {
        List <Transition> result = new ArrayList<>();
        for(Transition t : allOfThem)
            result.add(t.copyOfSalVersion());
        return result;
    }
    
    public Transition copyOfSalVersion() {
        Transition result = new Transition(getIdentifier());
        result.arity = arity;
        result.transitionLabel = transitionLabel;
        result.initialStateTest = initialStateTest;
        result.initialLabelTest = initialLabelTest;
        result.guard = guard;
        result.overAndUnderFlowTests = overAndUnderFlowTests;
        result.updates =  new ArrayList<>(updates);
        return result;
    }
    
    List <Transition> createVersions(SAL sal, int number) throws IsabelleException, FileException  {
        assert number>1;
        IsabelleException.reportIf(number>26,"Siobhan hadn't thought of there being more than 26 clones");
        List <Transition> result = new ArrayList<>();
        for(int i=0; i<number; i++) {
            Transition clone = copyOfSalVersion();
            clone.setIdentifier(getIdentifier()+SAL.SYSTEM_MARKER+((char)('a'+i)));
            result.add(clone);
        }
        return result;
    }
                 
    static Transition newNullTransition(Assignment after)  {
        Transition t = new Transition("SINK_HOLE");
        t.addMove(null,after);
        t.updates.add(Assignment.newOne(IOVariable.THE_OUTPUT_VARIABLE));        
        return t;
    }
   
    public void translateInto(SAL sal) throws IsabelleException  {
        
        initialLabelTest = Assignment.newOne(SystemVariable.LABEL,transitionLabel);    
        overAndUnderFlowTests = null;
       
        IOVariable.setMaxes(
                arity, 
                (  outputs==null  ?  0  : outputs.size())); 
        if  (  updates != null  )  
            for (Assignment u : updates)  {
                if  (  u.getValue() instanceof ArithmeticExpression  )  {
                    if  (  overAndUnderFlowTests == null  )  
                        overAndUnderFlowTests = new ArrayList<>();
                    overAndUnderFlowTests.add(new OverflowExpression(u.getValue()));
                }
            }        
         updates.add(Assignment.newOne(IOVariable.THE_OUTPUT_VARIABLE, outputs));
        
    } 
       
    //::::::::::::::::::::::::::: Output as SAL
    
    public void outputDefinitionAsSAL() throws IsabelleException, FileException {
        
        outputSALLine(getIdentifier().toUpperCase(), Token.COLON);  
        
        increaseMarginOnSALOutput();//double indent
        
            increaseMarginOnSALOutput();//double indent
            if  (  initialStateTest == null  ) 
                outputSALLine(Token.ELSE);
            else {
                initialStateTest.outputAsSAL();
                outputSAL(Token.AND);
                initialLabelTest.outputAsSAL();                          
                outputSAL(Token.AND);
                IOVariable.outputArityTest(arity);
                if  (  guard != null  )
                    for (Guard p : guard)  {
                        outputSAL(Token.AND);
                            p.outputAsSAL();
                    }
                if  (  overAndUnderFlowTests != null  )
                    for (OverflowExpression p : overAndUnderFlowTests)  {
                        outputSAL(Token.AND);
                        p.outputAsSAL(false);
                    }
                outputNewLineInSAL();
            }
            decreaseMarginOnSALOutput();
            outputSALLine(Token.GUARDED_BY);
            
            increaseMarginOnSALOutput();
                for(Assignment u : updates) 
                    u.updateOutputAsSAL(updates.indexOf(u)==updates.size()-1);
                
            decreaseMarginOnSALOutput();
            
        decreaseMarginOnSALOutput();
    }

    //::::::::::::::::::::::::::: Output as Dot
    
    String getLabelAsString() {  
        if  (  transitionLabel == null  )  return null;
        return transitionLabel.getIdentifier();  
    }
    
    int getArity() {return arity; }
    
    List<Guard> getGuard() {  return guard;  }
        
    List<Assignment> getUpdates() {  return updates;  }
    
    public SystemConstant  initialState() {
        if  (  initialStateTest == null  )  return null;
        return ((ConstantExpression)
                (initialStateTest.getValue()))
                .getState();
    }
            
}//Transition class
    
    

