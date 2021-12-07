package isabelle2sal;

import static isabelle2sal.Parser.*;
/**
 * @author sdn
 */

public class Skip extends Exception {
    
    public static void everything() throws Skip {
        throw new Skip();    
    }
    
    public static void ifNextTokenIs(Token t) throws Skip  {
        if  (  nextTokenIs(t)  )
            throw new Skip();
    }
    
    public static void ifNextTokenIsOneOf(Token ... tokens) throws Skip, IsabelleException  {
        for (Token t : tokens) 
            if  (  nextTokenIs(t)  )   throw new Skip();       
    }
    
    public static void unlessNextTokenIsOneOf(Token ... tokens) throws Skip, IsabelleException  {
        for (Token t : tokens) 
            if  (  nextTokenIs(t)  )  return; 
        throw new Skip();
    }
    
    public static void unlessNextTokenIs(Token t) throws Skip, IsabelleException  {
         if  (  ! nextTokenIs(t)  )
              throw new Skip();
    }
    
    public static void unlessNextTokenWas(Token t) throws Skip, IsabelleException, FileException  {
         if  (  ! acceptedTokenWas(t)  )
              throw new Skip();
    }
    
    private Skip () { 
        super("");
    }

}

    

