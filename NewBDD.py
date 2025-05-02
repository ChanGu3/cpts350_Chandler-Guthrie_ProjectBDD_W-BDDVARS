import math
from pyeda.inter import *


class MyBDD:
    
    # a node u->v is always the only edges so the boolExpr representation is always And(u, v)
    # EX.
    # 0 is a node and 1 is a node, 
    # to get a edge from 0 to 1 it is And(~u, v)
    # to get a edge from 1 to 0 it is And(u, ~v)
    def __init__(self, numOfNodes):
        self.__numOfNodes = numOfNodes
        self.__numOfBits = math.ceil(math.log2(numOfNodes)) ## should be fine
        self.__numOfBDDVars = self.__numOfBits * 2

        self.u = bddvars('u', self.__numOfBits)
        self.v = bddvars('v', self.__numOfBits)
        
        self.R = self.___CreateGrapgG()
        pass
    
    # Using the AStatement I transformed it into a one that can be operated on using smoothing for the exsistential quantifier 
    #   
    #   ∀u(IsPrime(u) → ∃v(IsEven(v) ∧ RR2star(u, v)))
    #   ~∃v ~(IsPrime(u) → ∃v(IsEven(v) ∧ RR2star(u, v))) # De Morgans Law
    #   ~∃v (IsPrime(u) ∧ ~∃v(IsEven(v) ∧ RR2star(u, v))) # De Morgans Law
    # returns boolExpr (with no free variables)
    def IsAStatementTrue(self):
        EvenStepEdges = self.RR2Star() # RR2star(u, v)
        
        Possible_Evens = self.__GetEvenExpr() # IsEven(v)
        Possible_Primes = self.__GetPrimeExpr() # IsPrime(u)
        
        result = Possible_Evens & EvenStepEdges # (IsEven(v) ∧ RR2star(u, v))
        
        result_smooth_e = result.smoothing(self.v) # ∃v(IsEven(v) ∧ RR2star(u, v))
        
        result_smooth_e_Not = ~result_smooth_e # ~∃v(IsEven(v) ∧ RR2star(u, v))
        
        result_smooth_e_Not_result = Possible_Primes & result_smooth_e_Not # IsPrime(u) ∧ ~∃v(IsEven(v) ∧ RR2star(u, v))
        
        result_smooth_e_Not_result_smooth_p = result_smooth_e_Not_result.smoothing(self.u) # ∃v (IsPrime(u) ∧ ~∃v(IsEven(v) ∧ RR2star(u, v)))
        
        result_smooth_e_Not_result_smooth_p_Not = ~result_smooth_e_Not_result_smooth_p # ~∃v (IsPrime(u) ∧ ~∃v(IsEven(v) ∧ RR2star(u, v)))
        
        return  result_smooth_e_Not_result_smooth_p_Not
    
    # Checks if two nodes are connected by an edge in 1 step
    def RR(self, nodeU: int, nodeV: int):        
        return self.R.restrict(self.__GetFullPoint(nodeU, nodeV))

    # checks if a node is even using v boolVars since __GetEVENExpr depends on it
    def EVEN(self, node):
        # filters base on current node and any even node if it exists and inputting in the node input point gives a 1 that means the node existed after filtering making it true
        return (self.__ConvertBinaryNodeToExpr(node, self.v) & self.__GetEvenExpr()).restrict(self.__GetHalfPointV(node)).is_one()
    
    # checks if a node is prime using u boolVars since __GetPrimeExpr depends on it
    def PRIME(self, node):
        # filters base on current node and Prime nodes if it exists after filtering and inputting in the node input point gives a 1 that means the node existed after filtering making it true
        return (self.__ConvertBinaryNodeToExpr(node, self.u) & self.__GetPrimeExpr()).restrict(self.__GetHalfPointU(node)).is_one()

    # Checks if two nodes are connected by edges in 2 step
    def RR2(self, nodeU: int, nodeV: int):    
        __R0R = self.__R0R(self.R, self.R)
        return __R0R.restrict(self.__GetFullPoint(nodeU, nodeV))
    
    # Does a Fixed Point on operation R getting all reachability from a node to another node in R
    # returns boolExpr 
    def FixedPoint(self): 
        print("Performing FixedPoint...")   
        H = self.R
        
        i = 0
        while True:
            print(f"{i}", end=" ", flush=True)
            Hp = H
            H = Hp | self.__R0R(Hp, self.R)

            i = i + 1
            if H.equivalent(Hp):
                break 
            
        print()
        print("Completed FixedPoint!")    
        print()  
        return H     
    
    #  Gets even number of step edges using Fixed Point and ends when H == H` 
    #   this collects each H` o R that is an even step thats transitive by
    #   doing a seperate operation similar, but does not do the
    #   combination step of H = H | (H` o R) it only gives the next set of transitives (or exactly # of steps)
    #   H = (H o R).
    # returns boolExpr. 
    def RR2Star(self):    
        print("Performing RR2Star...")   
        H = self.R
        E = self.R
        EvenTransitive = None
        i = 2
        while True:
            print(f"{i-2}", end=" ", flush=True)
            Ep = E
            Hp = H
            
            Hp_R = self.__R0R(Hp, self.R)
            H = H | Hp_R
            E = self.__R0R(Ep, self.R)
            
            if H.equivalent(Hp):
                break 
            
            if i % 2 == 0:
                if EvenTransitive is None:
                    EvenTransitive = E
                else:
                    EvenTransitive = EvenTransitive | E
            i = i + 1
            
        print()
        print("Completed RR2Star!")   
        print()
        return EvenTransitive                  

    # Creates a Dot File Of the Current R
    def WriteADotFile(self, nameOfFile: str):
        # turns R into dot string form
        #R_BDD = expr2bdd(self.R) 
        
        dot_str = str(self.R.to_dot())
    
        # Write Dot to file to compile into png in terminal
        with open(f"{nameOfFile}.dot", "w") as f:
            f.write(dot_str)
        return

    # R o R operation using MyExpr u and v exprvars and the count of bits the u and v have.
    #   gives all possible transitives from one boolExpr to another boolExpr
    # returns boolExpr
    def __R0R(self, R1, R2):
        z = bddvars('z', self.__numOfBits)

        # treat v as z 
        R2_uz = R2.compose({ self.v[i]: z[i] for i in range(len(self.v)) })
        # then make u as v 
        R2_vz = R2_uz.compose({ self.u[i]: self.v[i] for i in range(len(self.u)) })

        # summary to here from start: since we are treating u as v in R2_vz we get somthing like this 
        #   R1 is u&v and R2 now composed is v&z

        # there are two possibilities for this And operation now
        #   First Possibility: When anding these together if all the boolvars in R1 that is v is the same as the ones in R2 that is v we will get u&v&z
        #   Second Possibility: however if at least one boolvar in R1 that is in the boolvars v is the not the same as one of the boolvars in R2 that is in v, 
        #       (where i is a index of a a singular boolvar), v[i] & not(v[i]) this will be trivially false since both cannot be true filtering out
        #       the u&v & v&z where v is not the same.
        composed = R1 & R2_vz

        # This smoothing process takes the u&v&z's in composed (which can also be seen as u->v->z) and removing the middle man
        # by creating every possible path from u->z that v could have made.
        composed_smoothed = composed.smoothing(self.v)

        # z is considered a v node since we always represent v as a to node in the BoolExpr so change the z back into v giving us the transitive of 
        # u->v->z to u->z to our correct representation u->v 
        result = composed_smoothed.compose({ z[i]: self.v[i] for i in range(len(z)) })
  
        return result

    # Converts two nodes into a point which is a possible input within the space that results in 1 or 0 when restricting the point in a boolExpr
    # returns point
    def __GetFullPoint(self, nodeU: int, nodeV: int):
        
        # Make sure the intValue is not negative
        if nodeU < 0 | nodeV < 0:
            print("A node cannot have a negative value")
            return None
        
        # When nodeU is 0 no need to check this since __numOfBits > 0 can make a node representing 0
        if nodeU != 0:
            # Make sure both node values are not greater than the current values
            if self.__numOfBits < (math.floor(math.log2(nodeU)) + 1):
                print("nodeU is greater than what the current variables can represent")
                return None
            
        # When nodeU is 0 no need to check this since __numOfBits > 0 can make a node representing 0
        if nodeV != 0:
            # Make sure both node values are not greater than the current values
            if self.__numOfBits < (math.floor(math.log2(nodeV)) + 1):
                print("nodeV is greater than what the current variables can represent")
                return None
        
        point = {}
            # loop through each bit converting bit to bddvar 
        n = 1 # start with least significant bit  
        for i in range(self.__numOfBits-1, -1, -1):
            if n & nodeU != 0: # if bit is 1
                    point.update({self.u[i]: 1})
            else: # if bit is 0
                    point.update({self.u[i]: 0})
                    
            if n & nodeV != 0: # if bit is 1
                    point.update({self.v[i]: 1})
            else: # if bit is 0
                    point.update({self.v[i]: 0})
                    
            n <<= 1 # shift bits towards MSB by 1
        return point

    # Converts a node into a point of U which is a possible input within the space that results in 1 or 0 when restricting the point in a boolExpr
    # returns point
    def __GetHalfPointU(self, nodeU: int):
        
        # Make sure the intValue is not negative
        if nodeU < 0:
            print("A node cannot have a negative value")
            return None
        
        # When nodeU is 0 no need to check this since __numOfBits > 0 can make a node representing 0
        if nodeU != 0:
            # Make sure both node values are not greater than the current values
            if self.__numOfBits < (math.floor(math.log2(nodeU)) + 1):
                print("nodeU is greater than what the current variables can represent")
                return None
        
        point = {}
            # loop through each bit converting bit to bddvar 
        n = 1 # start with least significant bit  
        for i in range(self.__numOfBits-1, -1, -1):
            if n & nodeU != 0: # if bit is 1
                    point.update({self.u[i]: 1})
            else: # if bit is 0
                    point.update({self.u[i]: 0})
                    
            n <<= 1 # shift bits towards MSB by 1
        
        return point

    # Converts a node into a point of V which is a possible input within the space that results in 1 or 0 when restricting the point in a boolExpr
    # returns point
    def __GetHalfPointV(self, nodeV: int):
        
        # Make sure the intValue is not negative
        if nodeV < 0:
            print("A node cannot have a negative value")
            return None
        
        # When nodeU is 0 no need to check this since __numOfBits > 0 can make a node representing 0
        if nodeV != 0:
            # Make sure both node values are not greater than the current values
            if self.__numOfBits < (math.floor(math.log2(nodeV)) + 1):
                print("nodeV is greater than what the current variables can represent")
                return None
        
        point = {}
            # loop through each bit converting bit to bddvar 
        n = 1 # start with least significant bit  
        for i in range(self.__numOfBits-1, -1, -1):
            if n & nodeV != 0: # if bit is 1
                    point.update({self.v[i]: 1})
            else: # if bit is 0
                    point.update({self.v[i]: 0})
                    
            n <<= 1 # shift bits towards MSB by 1
        
        return point


    # converts a number using a exprVars where the number of exprVars are the same as the number of bits that can represent the int
    #   into a node as a boolExpr
    # returns boolExpr
    def __ConvertBinaryNodeToExpr(self, intValue: int, exprVars: farray):
        nodeExpr = None

        # Make sure at least one exprVar
        if len(exprVars) <= 0:
            print("No ExprVar to evaluate")
            return None
        
        # Make sure the intValue is not negative
        if intValue < 0:
            print("Value cannot be negative")
            return None
        
        # When value is 0 no need to check this since len(bbdVars) > 0 can make a node representing 0
        if intValue != 0:
            # length of variables must match the lengh of using bit in int
            if len(exprVars) < (math.floor(math.log2(intValue)) + 1):
                print("The value is greater than what the variables can represent")
                print(f"{len(exprVars)} < {(math.floor(math.log2(intValue)) + 1)} ||| intValue = {intValue}")
                return None
        
        # loop through each bit converting bit to bddvar 
        n = 1 # start with least significant bit  
        for i in range(len(exprVars)-1, -1, -1):
            if n & intValue != 0: # if bit is 1
                if i == len(exprVars)-1: # least significant bit
                    nodeExpr = exprVars[i]
                else:
                    nodeExpr = nodeExpr & exprVars[i]
            else: # if bit is 0
                if i == len(exprVars)-1: # least significant bit
                    nodeExpr = ~exprVars[i]
                else:
                    nodeExpr = nodeExpr & ~exprVars[i]
            n <<= 1 # shift bits towards MSB by 1
        
        return nodeExpr

    # Creates an edge between a nodeU to a nodeV
    # returns boolExpr
    def ___MakeEdgeToExpr(self, nodeU, nodeV):
        return nodeU & nodeV

    # Creates the edges following the conditions
    #   For all 0 ≤ i, j ≤ 31, there is an edge from node i to node j iff (i + 3)%32 = j%32 or (i + 8)%32 = j%32.
    # returns boolExpr
    def ___CreateGrapgG(self):
        R = None

        for i in range(0 , 32):
            for j in range(0, 32):
                if ((i + 3) % 32) == (j % 32) or ((i + 8) % 32) == (j % 32):
                    if R is None:
                        R = self.___MakeEdgeToExpr(self.__ConvertBinaryNodeToExpr(i, self.u), self.__ConvertBinaryNodeToExpr(j, self.v))
                    else:
                        R = R | self.___MakeEdgeToExpr(self.__ConvertBinaryNodeToExpr(i, self.u), self.__ConvertBinaryNodeToExpr(j, self.v))
        return R

    # uses Not becuase not(v[LSB]) & v[LSB] filters any with this possibility since both cannot be true make the expr trivally false
    # vice versa not(v[LSB]) & not(v[LSB]) is trivally just not(v[LSB]) so it doesnt change
    # return boolExpr
    def __GetEvenExpr(self):        
        # Only the LSB since it is used to make a number even or odd. 
        return ~self.v[self.__numOfBits-1]
    
    # Uses filtering by getting the primes hard coded since 2 isnt allowed with the primes so only up to 32 currently
    #   Or's each prime node as a boolExpr
    # returns boolExpr
    def __GetPrimeExpr(self):
        R = None

        # Or's all primes as node binary representation
        for i in range(0 , self.__numOfNodes):
                if self.__IsPrime(i):
                    if R is None:
                        R = self.__ConvertBinaryNodeToExpr(i, self.u)
                    else:
                        R = R | self.__ConvertBinaryNodeToExpr(i, self.u)
        return R

    # if a number is within this set it returns true otherwise false.
    def __IsPrime(self, node):
        return node == 3 or node == 5 or node == 7 or node == 11 or node == 13 or node == 17 or node == 19 or node == 23 or node == 29 or node == 31
    
    # TESTING RR2Star EVENS STEPS ONLY
    def ____TestEven____(self):
        EvenStepEdges = self.RR2Star()
        print("Should Be = True")
        print(f"EvenStepEdgesRR?(27, 3) = {EvenStepEdges.restrict(self.__GetFullPoint(27,3)).is_one()}") # REACHED IN 10 STEPS NOT THE NORMAL 1 STEP (Possible has more even step reachablity)
        print(f"EvenStepEdgesRR?(27, 6) = {EvenStepEdges.restrict(self.__GetFullPoint(27,6)).is_one()}") # REACHED IN 2 STEPS (Possible has more even step reachablity)
        print(f"EvenStepEdgesRR?(27, 12) = {EvenStepEdges.restrict(self.__GetFullPoint(27,12)).is_one()}") # REACHED IN 4 STEPS (Possible has more even step reachablity)
        print(f"EvenStepEdgesRR?(27, 18) = {EvenStepEdges.restrict(self.__GetFullPoint(27,18)).is_one()}") # REACHED IN 6 STEPS (Possible has more even step reachablity)
        print(f"EvenStepEdgesRR?(27, 24) = {EvenStepEdges.restrict(self.__GetFullPoint(27,24)).is_one()}") # REACHED IN 8 STEPS (Possible has more even step reachablity)
        print("Should Be = False")
        print(f"EvenStepEdgesRR?(27, 9) = {EvenStepEdges.restrict(self.__GetFullPoint(27,9)).is_one()}") # REACHED IN 3 STEPS (Possible has more odd step reachablity)
        print(f"EvenStepEdgesRR?(27, 15) = {EvenStepEdges.restrict(self.__GetFullPoint(27,15)).is_one()}") # REACHED IN 5 STEPS (Possible has more odd step reachablity)
        print(f"EvenStepEdgesRR?(27, 21) = {EvenStepEdges.restrict(self.__GetFullPoint(27,21)).is_one()}") # REACHED IN 7 STEPS (Possible has more odd step reachablity)
        return

def Test():
    myExpr = MyBDD(32)
    
    myExpr.____TestEven____()

def main():
    myExpr = MyBDD(32)
    
    print(f"RR(27, 3) is {myExpr.RR(27, 3).is_one()}")
    print(f"RR(16, 20) is {myExpr.RR(16, 20).is_one()}")
    print(f"EVEN(14) is {myExpr.EVEN(14)}")
    print(f"EVEN(13) is {myExpr.EVEN(13)}")
    print(f"PRIME(7) is {myExpr.PRIME(7)}")
    print(f"PRIME(2) is {myExpr.PRIME(2)}")
    
    print()
    
    print(f"RR2(27, 6) is {myExpr.RR2(27, 6).is_one()}")
    print(f"RR2(27, 9) is {myExpr.RR2(27, 9).is_one()}")
    
    print()
    
    AStatement = myExpr.IsAStatementTrue()
    print(f"Is AStatement True? : {AStatement.is_one()}")
        
    return 

main()