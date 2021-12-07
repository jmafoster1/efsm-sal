package isabellesal;


/**
 *
 * @author sdn
 */

public class IsabelleException extends Exception {
    
    String failureFor(String fileName) {
        return "Unsuccessful translation. Error_" + fileName + " has been created"; 
    }
    
    static void reportIf (boolean test, String errorMessage) throws IsabelleException, FileException {
        if  (  test  )  {
            Generator.finishSALOutputSuccessfully(false);
            throw new IsabelleException("It was impossible to generate a complete SAL file because "+errorMessage);
        }
    }    

    IsabelleException (String reason) {
        super(reason);
    }

}


