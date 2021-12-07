package isabelle2sal;

import static isabelle2sal.Generator.*;
import static isabelle2sal.Parser.*;
import java.util.*;

/**
 *
 * @author sdn
 */
public class Lemma  {              
    
    //::::::::::::::::::::::::::: The Internal Representation
    
    private static List<Lemma> theLemmas = new ArrayList<>();
    
    public static Lemma[] theTheorems() {
        return theLemmas.toArray(new Lemma[0]);        
    }   
        
    static void clearAll() { 
        theLemmas.clear();
    }  
    
    String identifier;
    EFSM efsm;
    LTL ltl; 
     
    Map<String, FreeVariable> freeValues = new HashMap<>();
    
    FreeVariable freeVariableCalled(String i, Type t)  {
        assert t != null;
        if  (  ! freeValues.containsKey(i)   ) 
            freeValues.put(i, new FreeVariable(i,t));
        if  (  t != Type.STRING  )  NumericConstant.neverStringify = true;
        return freeValues.get(i);       
    }
    
    String getIdentifier() {  return identifier;  }

    private Lemma (String i) {
        identifier = i;      
    }

    //::::::::::::::::::::::::::: Creation from Isobelle Source code
    
    static void readOneIn() throws IsabelleException, Skip, FileException {
        assert nextTokenIsOneOf(Token.LEMMA, Token.THEOREM);
        acceptToken();  //lemma and theorem are interchangable for the purposes of the translation
        
        Skip.ifNextTokenIs(Token.QUOTE);  //skipping a lemma with no name
        
        nextTokenMustBe(Token.NEW_WORD);
        Lemma theNewOne = new Lemma(acceptedWord());
                
        Skip.unlessNextTokenWas(Token.COLON);    
        Skip.unlessNextTokenWas(Token.QUOTE);
        
        if  (  !  nextTokenIsOneOf(LTL.SIMPLE_STARTERS)  )
            Skip.everything();
        
        theNewOne.ltl = LTL.readSimpleOneIn(theNewOne);
        
        //find efsm in final bracketed clause
        Skip.unlessNextTokenWas(Token.OPENING_ROUND_BRACKET);    
        Skip.unlessNextTokenWas(Token.WATCH);   
        Skip.unlessNextTokenIs(Token.EFSM_NAME);
        theNewOne.efsm = EFSM.theOneCalled(acceptedWord());
        acceptToken();  //could be any identifier        
        accept(Token.CLOSING_ROUND_BRACKET);
        
        accept(Token.QUOTE);

        theLemmas.add(theNewOne);
        
    }
              
    //::::::::::::::::::::::::::: Translating from isablle to sal

    void translateInto(SAL sal)  {
        assert ltl != null;
        assert sal != null;
        ltl.translateInto(sal);
    }
        
    //::::::::::::::::::::::::::: Output as SAL
    
    void outputInSAL() throws IsabelleException, FileException { 
        increaseMarginOnSALOutput();
            outputSAL(this, Token.COLON, Token.THEOREM, efsm, "|-");
            
            if  (  ! freeValues.isEmpty()  ) {
                List <String> names = new ArrayList<>(freeValues.keySet());
                outputSAL(Token.FORALL, Token.OPENING_ROUND_BRACKET);
                boolean first = true;
                for (String f : names)  {
                    if  (  first )  first = false;
                    else  outputSAL(Token.COMMA);
                    outputSAL(f, Token.COLON,  freeValues.get(f).getType());
                }
                outputSAL (Token.CLOSING_ROUND_BRACKET, Token.COLON);
            }

            outputSALLine();
            increaseMarginOnSALOutput();
                ltl.outputAsSAL();
                outputSAL(Token.SEMICOLON);
            decreaseMarginOnSALOutput();
            outputBlankLineInSAL();
        decreaseMarginOnSALOutput();
    }
        
}
