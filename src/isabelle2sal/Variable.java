package isabelle2sal;

import static isabelle2sal.Generator.*;
import static isabelle2sal.Parser.*;

/**
 * Deals with the internal representation of variables and their creation
 * from Isobelle and their export into SAL
 * @author sdn
 */
public abstract class Variable {
    
    //::::::::::::::::::::::::::: The Internal Representation
    
    static void clearEverything()  {
        //Used when translating multiple files to purge the previous internal version
        IOVariable.clear();
        RegisterVariable.maxSubscript = 0;
    }
    
    private String identifier = null;
    String getIdentifier() {  return identifier;  }

    private Type type; 
    Type getType() {  return type;  }
    void setType(Type t)  {  type = t;  }
    
    void makeInteger() throws IsabelleException, FileException  {
        //Some integers can be strings to reduce SAL state space
        if  (  type == null  ) 
            setType(Type.ISABELLE_INTEGER_AS_INTEGER);
        else
            switch (type) {
                case ISABELLE_INTEGER_AS_STRING :
                    setType(Type.ISABELLE_INTEGER_AS_INTEGER);
                case ISABELLE_INTEGER_AS_INTEGER : return;
                case ISABELLE_STRING :
                    reportAnError("that should have been an integer");
            }
    }
       
    protected Variable (String i) {  
        identifier = i;  
        type = null;
    }
    
    //::::::::::::::::::::::::::: Creation from Isobelle Source code
    
    static Variable readInName(Object context) throws IsabelleException, FileException {

        accept(Token.OPENING_ROUND_BRACKET);
        
        if  (  context instanceof Lemma  ) //so an ltl not a transition
            nextTokenMustBeOneOf(Token.IP, Token.RG, Token.OP); 
        else
            nextTokenMustBeOneOf(Token.REGISTER, Token.INPUT);
        Token token  = acceptedToken();
        
        nextTokenMustBe(Token.NUMBER);
        int subscript = (int)acceptedNumber();         
        if  (  subscript < 0  )
            reportAnError("the subscript must be positive or zero");
        
        accept(Token.CLOSING_ROUND_BRACKET);
        
        switch  (  token.toString().charAt(0) ) {
            case 'I' : 
                return IOVariable.input(subscript, context);   
            case 'R' : 
                return RegisterVariable.numbered((int)subscript, context);   
            case 'O' : 
                return IOVariable.output(subscript);
            default : assert false : token;
        }  
        return null;
        
    }    
    
    //::::::::::::::::::::::::::: Output as SAL
    
    static void declareVariablesInSAL() throws IsabelleException, FileException {
        SystemVariable.declareBothInSAL();
        RegisterVariable.declareAllInSAL();
        IOVariable.declareBothInSAL();
    }
    
    static void initializeVariablesInSAL() throws IsabelleException, FileException {
        //The variable initializations in a sal module
        SystemVariable.initializeState();
        outputSALLine(Token.AND);   
        IOVariable.initializeOutputInSAL();
        RegisterVariable.initializeAll();
    }
       
    abstract public void outputAsSAL(boolean withSome) throws IsabelleException, FileException;  
    
    //::::::::::::::::::::::::::: Output as Dot
    
    abstract public String toDot();
       
}

class FreeVariable extends Variable {
    
    //::::::::::::::::::::::::::: The Internal Representation
       
    FreeVariable (String i, Type t)  {  
        super(i);  
        setType(t);
    }
        
    //::::::::::::::::::::::::::: Creation from Isobelle Source code
    
    static FreeVariable readOneIn(Object context, Type t) throws IsabelleException, FileException  {
        assert context instanceof Lemma;
        assert t != null;
        
        nextTokenMustBeOneOf(Token.NEW_WORD, Token.FREE_VARIABLE_NAME);
        if  (  nextTokenIs(Token.NEW_WORD)  )            
            addToDictionary(nextWord(), Token.FREE_VARIABLE_NAME);

        return ((Lemma)context).freeVariableCalled(acceptedWord(),t);      
    }
    
    
    //::::::::::::::::::::::::::: Output as SAL
    
    @Override
    public void outputAsSAL(boolean withSome) throws IsabelleException, FileException {
        if  (  getType() == Type.VALUE  )
            outputSALWithSomeIfNecessary(getIdentifier(), withSome);
        else  {
            if  (  withSome  )  outputSAL(Token.SOME, Token.OPENING_ROUND_BRACKET);
            if  (  getType() == Type.STRING  )
                outputSAL(Token.STR);
            else 
                outputSAL(Token.NUM);
            outputSAL(Token.OPENING_ROUND_BRACKET, getIdentifier(), Token.CLOSING_ROUND_BRACKET);        
            if  (  withSome  )  outputSAL(Token.CLOSING_ROUND_BRACKET);
        }
    }
    
    //::::::::::::::::::::::::::: Output as Dot    
    
    @Override
    public String toDot() { assert false;  return null;  }
    
}

class IOVariable extends Variable {
    
    //::::::::::::::::::::::::::: The Internal Representation

    private static enum Direction {
        INPUT, OUTPUT;
        
        private int max;
        
        int getMax() {   return max;  }
        
        void setMax(int m)  {  if  (  m > max  )  max = m;  }
        
        String initial() {  return name().substring(0,1).toLowerCase();  }
        
        String toSequence()  {
            return name().toLowerCase()+"_sequence ! ";
        }
        
        String toEmptySequence()  {
            return toSequence()+"empty";
        }
        
        String elementType() { 
            return (  this == OUTPUT ? "Option" : "Value" );
        }
        
        String typeDeclaration() {
            return name().toLowerCase()+"_sequence : CONTEXT = sequence {"+
                    "B_"+elementType().toUpperCase()+", "+
                    elementType()+"BB, " +
                    Math.max(1, max)+
                    "};";
        }
        
        static void clear() {
            INPUT.max=1;        
            OUTPUT.max=1;        
        }
      
    }
    
    static IOVariable THE_OUTPUT_VARIABLE = new IOVariable(Direction.OUTPUT, null);
    static IOVariable THE_INPUT_VARIABLE = new IOVariable(Direction.INPUT, null);
    static IOVariable NONE = new IOVariable(Direction.OUTPUT, null);
    
    static void clear() {
        Direction.clear();        
    }
        
    private Integer subscript = null;
    
    private Direction direction = null;
    
    private IOVariable (Direction d, Integer s) {
        super(d.initial());
        direction = d;
        subscript = s;
    }
        
    //::::::::::::::::::::::::::: Creation from Isobelle Source code
    
    public static IOVariable input(int s, Object context)  {
        assert s >= 0;
        if  (  context instanceof Lemma  )  //ltl version
            return new IOVariable(Direction.INPUT, s);
        if  (  ! ((Transition)context).hasInput(s)  )
            ((Transition)context).addInput(s, new IOVariable(Direction.INPUT, s));
        return ((Transition)context).getInput(s);
    }
       
    public static IOVariable output(int s)  {
        assert s >= 0;
        //ltl version so free variable
        return new IOVariable(Direction.OUTPUT, s);
    }
       
    //::::::::::::::::::::::::::: Translating from isablle to sal
    
    static void setMaxes(int i, int o) {  
        Direction.INPUT.setMax(i); 
        Direction.OUTPUT.setMax(o);
    }
    
    //::::::::::::::::::::::::::: Output as SAL
    
    static void declareSequenceTypesInSAL() throws IsabelleException, FileException {
        for (Direction d : Direction.values())
            outputSALLine(d.typeDeclaration());
    }
        
    static void declareBothInSAL() throws IsabelleException, FileException  {
        for (Direction d : Direction.values())
            outputSALLine(d.name(), d.initial(), Token.COLON, 
                    d.toSequence()+"Sequence"); 
    }    
        
    static void initializeOutputInSAL() throws IsabelleException, FileException {
        outputSAL(Direction.OUTPUT.initial(), Token.EQUALS, 
                Direction.OUTPUT.toEmptySequence());   
    }
        
    static void outputArityTest(int arity) throws IsabelleException, FileException  {
        outputSAL( 
                Direction.INPUT.toSequence()+"size?(i)", 
                Token.EQUALS, arity);
    }
    
    public String nullValueInSAL()  {
        return direction.toEmptySequence();
    }
       
    public void startExplicitSequence() throws IsabelleException, FileException {
        outputSAL(direction.toSequence()+"insert", 
                Token.OPENING_ROUND_BRACKET);
    }
    
    public void finishExplicitSequence(int elementCount) throws IsabelleException, FileException {
        outputSAL(direction.toEmptySequence());
        for (int i=0; i<elementCount; i++)
            outputSAL(Token.CLOSING_ROUND_BRACKET);
    }
    
    @Override
    public void outputAsSAL(boolean withSome) throws IsabelleException, FileException {
        String inSal = getIdentifier();    
        if  (  subscript != null )
            inSal += "("+subscript+")";
        outputSALWithSomeIfNecessary(inSal, withSome);
    }
    
    //::::::::::::::::::::::::::: Output as Dot
    
    @Override public String toDot() {
        return  getIdentifier().toLowerCase() + 
                "<sub>" + String.valueOf(subscript) + "</sub>";
    }
       
}

class RegisterVariable extends Variable {
    
    //::::::::::::::::::::::::::: The Internal Representation
    
    final private static String REGISTER_NAME = "r"+SAL.SYSTEM_MARKER;

    static int maxSubscript=0;
    
    private int subscript;
    
    private RegisterVariable (int s) {
        super(REGISTER_NAME+s);
        subscript = s;
    }
    
    //::::::::::::::::::::::::::: Creation from Isobelle Source code
        
    public static RegisterVariable numbered(int s, Object context)  {
        assert s >= 0;
        if  (  context instanceof Lemma )  return 
            new RegisterVariable(s);   
        maxSubscript = Math.max(s, maxSubscript);
        if  (  !  ((Transition)context).hasRegister(s)  )
            ((Transition)context).addRegister(s, new RegisterVariable(s));
        return ((Transition)context).getRegister(s);
    }
    
    //::::::::::::::::::::::::::: Output as SAL
            
    static void declareAllInSAL() throws IsabelleException, FileException {
        for (int r = 1; r<=maxSubscript; r++) 
            outputSALLine("LOCAL", REGISTER_NAME+r, Token.COLON, "OPTION");
    }
    
    static void initializeAll() throws IsabelleException, FileException {
        for (int r=1; r<=maxSubscript; r++)  {
            outputSALLine(Token.AND);
            outputSAL(REGISTER_NAME+r, Token.EQUALS, "None");
        }
    }
    
    @Override
    public void outputAsSAL(boolean withSome) throws IsabelleException, FileException {
        outputSAL(getIdentifier());        
    }
    
    //::::::::::::::::::::::::::: Output as Dot
    
    @Override
    public String toDot() {
        return  "r<sub>" + String.valueOf(subscript) + "</sub>";
    }
               
}

class SystemVariable extends Variable {
    
    //::::::::::::::::::::::::::: The Internal Representation
    
    static final SystemVariable LABEL = 
            new SystemVariable("label");
    static final SystemVariable STATE =  
            new SystemVariable("cfstate");
    
    private SystemVariable (String name) {
        super(name);
    }
    
    //::::::::::::::::::::::::::: Output as SAL

    static void declareBothInSAL() throws IsabelleException, FileException {
        outputSALLine("INPUT", LABEL, Token.COLON, Type.LABEL);
        outputSALLine("LOCAL", STATE, Token.COLON, Type.STATE);
    }
    
    static void initializeState() throws IsabelleException, FileException {
        outputSAL(STATE, Token.EQUALS, SystemConstant.stateConstantNameFor(0));
    }
    
    @Override
    public void outputAsSAL(boolean withSome) throws IsabelleException, FileException {
        outputSAL(getIdentifier());        
    }
    
    //::::::::::::::::::::::::::: Output as Dot
    
    @Override
    public String toDot() { 
        assert false;
        return "Siobhan has got something wrong";
    }

}

