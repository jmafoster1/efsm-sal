
package dottoisabelle;

/**
 *
 * @author sdn
 */
public class DotException extends Exception{
    
    static void report(String error) throws DotException {
        Parser.reportAnError(error);
    }

    static void reportUnless(boolean test, String error) throws DotException {
        if  (  ! test  )  report(error);
    }

    static void reportIf(boolean test, String error) throws DotException {
        if  (  test  )  report(error);
    }

    DotException (String because) { 
        super("Failed to read in the dot file because "+because); 
    }
    
}
