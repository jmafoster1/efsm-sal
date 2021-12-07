package isabelle2sal;

import static isabelle2sal.Parser.*;
import java.util.*;

/**
 * Deals with constants
 * @author Siobhan
 */
public abstract class Constant  {
    
    //::::::::::::::::::::::::::: The Internal Representation
    
    static void clearAll() {
        NumericConstant.neverStringify = false;
        SystemConstant.clear();
    }
    
    private String identifier = null;    
    void setIdentifier(String s)  {  identifier = s;  }
    String getIdentifier() {  return identifier;  }
    
    private Type type;
    Type getType() { return type;  }
    
    Constant (String i, Type t)  {  
        identifier = i;
        type = t;
    }
    
    //::::::::::::::::::::::::::: Creation from Isobelle 
    
    static Constant readOneIn() throws IsabelleException, FileException {
        if  (  acceptedTokenWas(Token.NUM)  )
            return NumericConstant.readInNumber();
        else if  (  acceptedTokenWas(Token.STR)  )
            return SystemConstant.readInString();
        else
            nextTokenMustBeOneOf(Token.NUM, Token.STR);
        return null;    //never executed    
    }
    
    //::::::::::::::::::::::::::: Output as SAL
    
    abstract String useAsSAL();
    
    //::::::::::::::::::::::::::: Output as Dot
    
    abstract String toDot();
    
}

class BooleanConstant extends Constant {
    
    //::::::::::::::::::::::::::: The Internal Representation
    
    private BooleanConstant(Token t)  {  
        super(t.inSAL(), Type.BOOLEAN);
    }
    
    //::::::::::::::::::::::::::: Creation from Isobelle Source code
    
    public static BooleanConstant readItIn() throws IsabelleException, FileException {
        nextTokenMustBeOneOf(Token.TRUE, Token.FALSE);
        return new BooleanConstant(acceptedToken());
    }
    
    //::::::::::::::::::::::::::: Output as SAL
    
    @Override String useAsSAL() {  return getIdentifier();  }
    
    //::::::::::::::::::::::::::: Output as Dot
    
    @Override String toDot()  {  return getIdentifier();  }
    
}

class NumericConstant extends Constant  {
    
    //::::::::::::::::::::::::::: The Internal Representation
    
    private static Map<Long,  NumericConstant>  allNumericConstants = new HashMap<>();
    
    public static boolean neverStringify;
    
    private Long value;
    
    private boolean usedInArithmetic;   
    void hasBeenUsedInArithmetic()  {  usedInArithmetic = true;  }
    
    private NumericConstant(long c) {
        super (null, Type.ISABELLE_INTEGER_AS_INTEGER);  //No identifier
        value = c;
        usedInArithmetic = false;  
    }
    
    //::::::::::::::::::::::::::: Creation from Isobelle Source code
    
    static NumericConstant readInNumber() throws IsabelleException, FileException  {
        //Num has already been accepted
        int bracketCount=0;
        while (  acceptedTokenWas(Token.OPENING_ROUND_BRACKET)  )
            bracketCount++;
        
        int multiplier = (  acceptedTokenWas(Token.MINUS) ? -1 : 1);
        nextTokenMustBe(Token.NUMBER);
        long n = acceptedNumber() * multiplier;
        
        for (int i=bracketCount; i>0; i--)
            accept(Token.CLOSING_ROUND_BRACKET);
        
        if  (  ! allNumericConstants.containsKey(n)  )
            allNumericConstants.put(n,  new NumericConstant(n));
        return allNumericConstants.get(n);
    }
    
    //::::::::::::::::::::::::::: Translating from isablle to sal

    static long findMaximumAndMakeRestStrings() {
        //Find the maximum
        long max = 0;
        for (NumericConstant c : allNumericConstants.values()) {
            if  (  c.usedInArithmetic || neverStringify )
                max = Math.max(max, Math.abs(c.value));
        }
        
        if   (  !  neverStringify  )   {
            //Make the small ones numbers and the big ones strings
            List<Long> allNumbers = new ArrayList<>(allNumericConstants.keySet());
            Collections.sort(allNumbers);
            for (Long l : allNumbers  )
                if  (  l > max  )  {
                    String i = "NO"+SAL.SYSTEM_MARKER+l;
                    allNumericConstants.get(l).setIdentifier(i);
                    SystemConstant.addAsString(i);
                }
                else 
                    allNumericConstants.get(l).usedInArithmetic = true;
        }
        
        allNumericConstants.clear();
        
        return max;
    }
        
    //::::::::::::::::::::::::::: Output as SAL
    
    @Override String useAsSAL() {
        if  ( neverStringify || usedInArithmetic  )
            return "Num(" + String.valueOf(value) + ")";
        else 
            return "Str("+ getIdentifier() + ")";
    }         

    //::::::::::::::::::::::::::: Output as Dot
    
    @Override String toDot() {                  
        return String.valueOf(value);
    }
    
}

class SystemConstant extends Constant {
    
    //::::::::::::::::::::::::::: The Internal Representation
    
    private final static String STRING_MARKER = "String"+SAL.SYSTEM_MARKER;
    private final static String STATE_MARKER = "State"+SAL.SYSTEM_MARKER;
    
    final static SystemConstant NULL_STATE = 
            new SystemConstant("NULL_STATE", Type.STATE);
             
    private static Map<String, SystemConstant> allLabels = new HashMap<>();
    static Set <Integer>  allStates = new HashSet<> ();
    private static Map<String, SystemConstant> allStringConstants = new HashMap<>();
    
    static void clear() {
        allLabels.clear();
        allStringConstants.clear();
        allStates.clear();
    }
    
    private static List<SystemConstant> sortedValues(Map<String, SystemConstant> map) {
        List <String> temp = new ArrayList<>(map.keySet());
        Collections.sort(temp);
        List<SystemConstant> result = new ArrayList<>();
        for (String s : temp)
            result.add(map.get(s));
        return result;
    }
    
    private SystemConstant (String i, Type t) {
        super(i, t);
    }

    //::::::::::::::::::::::::::: Creation from Isobelle Source code
        
    static SystemConstant existingLabelFrom(String c) throws IsabelleException, FileException  {
        reportAnErrorUnless(allLabels.containsKey(c), c+" is not a label");
        return allLabels.get(c);
    }
        
    static SystemConstant fromLabel(String l) throws IsabelleException, FileException {
        if  (  !  allLabels.containsKey(l)  ) {
            for(char c : l.toCharArray()) 
                reportAnErrorUnless(
                        Character.isJavaIdentifierPart(c),
                        "The character "+c+" cannot be part of a transition label");
            allLabels.put(l, new SystemConstant(l, Type.LABEL));
        } 
        return allLabels.get(l);
    }
    
    static SystemConstant readInString() throws IsabelleException, FileException {
        //Str has already been accepted
        nextTokenMustBe(Token.STRING);
        String i = acceptedWord();
        if  (  !  allStringConstants.containsKey(i)  )
            allStringConstants.put(i, new SystemConstant(STRING_MARKER+i, Type.STRING));
        return allStringConstants.get(i);        
    }
    
    //::::::::::::::::::::::::::: Translating from isablle to sal

    static SystemConstant addAsString(String i)  { 
        //was a number
        assert ! allStringConstants.containsKey(i);
        allStringConstants.put(i,new SystemConstant(i, Type.STRING));
        return allStringConstants.get(i);
    }
    
    static List<SystemConstant> allStringConstants() {
        List<SystemConstant>  result =  sortedValues(allStringConstants);
        result.add(
                new SystemConstant(STRING_MARKER+"dummy"+SAL.SYSTEM_MARKER, 
                        Type.STRING));
        return result;
    }
    
    static List<SystemConstant> allStateConstants() {
        List<SystemConstant> result = new ArrayList<>();
        List<Integer> numbered = new ArrayList<>(allStates);
        Collections.sort(numbered);
        for(int i : numbered)
            result.add(new SystemConstant(STATE_MARKER+i, Type.STATE));
        result.add(NULL_STATE);
        return result;
    }
    
    static List<SystemConstant> allLabels() {
        return  sortedValues(allLabels);
    }
    
    static void includeState(Integer s) {
        if  (  allStates.contains(s)  )  return;
        allStates.add(s);
    }
    
    public static SystemConstant stateConstantFor(int i) { 
        return new SystemConstant(STATE_MARKER+i, Type.STATE);
    } 
            
    //::::::::::::::::::::::::::: Output as SAL
    
    public static String stateConstantNameFor(int i) {  
        return STATE_MARKER+i;
    }   
        
    @Override String useAsSAL() {   
        if  (  getType() == Type.STRING  )  
            return "Str("+getIdentifier()+")";
        else
            return getIdentifier();
    }            
    
    //::::::::::::::::::::::::::: Output as Dot
    
    @Override String toDot() { 
        final String PRIME = "\"";
        switch (getType()) {
            case STRING :
                return PRIME+
                   StringCharacters.unTranslationOf(getIdentifier().substring(STRING_MARKER.length()))+
                   PRIME;
            case STATE :
                return "s" + getIdentifier().substring((STATE_MARKER).length());
            case LABEL : return getIdentifier();
            default : assert false;
        }
        return null;
    }

}//System constant

