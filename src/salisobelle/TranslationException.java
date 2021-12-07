package salisobelle;

/**
 * @author sdn
 */

public class TranslationException extends Exception {
    
    static void report (String errorMessage) throws TranslationException {
        Generator.finishIsabelleOutputSuccessfully(false);
        throw new TranslationException("It was impossible to generate a complete SAL file because "+errorMessage);
    }
    
    static void reportIf (boolean test, String s) throws TranslationException {
        if  (  test  )  report(s);
    }    

    static void reportUnless (boolean test, String s) throws TranslationException {
        if  ( ! test  )  report(s);
    }    

    TranslationException (String because) { 
        super(because);
    }

}

    

