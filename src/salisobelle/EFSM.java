package salisobelle;

import static salisobelle.Parser.*;
import static salisobelle.Generator.*;
import java.util.*;

/**
 * Deals with an EFSM; 
 * @author sdn
 */
public class EFSM   {       
    
    //::::::::::::::::::::::::::: The Internal Representation
    
    static EFSM theOnlyOne = null;
    static EFSM theOnlyOne() {  return theOnlyOne;  }
    
    static void clearAll() {  theOnlyOne = null;  }
    
    private String identifier;
    String getIdentifier() {  return identifier;  }
                
    private List <Transition> theMoves;
    void addTransition(Transition t) {
       theMoves.add(t); 
    }
    
    private EFSM (String i) {  
        identifier = i;
        theMoves = new ArrayList<>();
    }
    
    //::::::::::::::::::::::::::: Input as SAL
    
    static void createOneCalled(String i) throws TranslationException  {
        reportAnErrorIf(
                theOnlyOne != null, 
                "This translator only accepts a single Module");
        addToDictionary(i, Token.EFSM_NAME);
        theOnlyOne = new EFSM(i);
    }
      
    //::::::::::::::::::::::::::: Output as Isabelle
            
    void outputAsIsabelle() throws TranslationException {
        final String TITLE = "\"transition_matrix\"";
        
        outputIsabelleLine(Token.DEFINITION, identifier, 
                Token.DOUBLE_COLON, TITLE, Token.WHERE);
        outputIsabelleLine(Token.OPENING_QUOTE, identifier, Token.EQUIV, 
                Token.OPENING_CURLY_BRACKET, Token.BAR);
        
        increaseMarginOnOutput();
        increaseMarginOnOutput();

        boolean first = true;
        for (Transition t : theMoves){
            if (  first  )  first = false;
            else   outputIsabelleLine(Token.COMMA);
            t.outputItsMove();              
        }
        outputIsabelleLine();
        
        decreaseMarginOnOutput();
        outputIsabelleLine(Token.BAR, Token.CLOSING_CURLY_BRACKET, Token.CLOSING_QUOTE);
        decreaseMarginOnOutput();
        outputBlankLineInIsabelle();
    }

}
