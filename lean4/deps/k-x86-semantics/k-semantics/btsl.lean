def btsl1 : instruction :=
  definst "btsl" $ do
    pattern fun (v_3227 : imm int) (v_3229 : reg (bv 32)) => do
      v_6242 <- getRegister v_3229;
      v_6245 <- eval (sext (bv_and (handleImmediateWithSignExtend v_3227 8 8) (expression.bv_nat 8 31)) 32);
      setRegister (lhs.of_reg v_3229) (bv_or v_6242 (extract (shl (expression.bv_nat 32 1) v_6245) 0 32));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_6242 v_6245) 31);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3233 : reg (bv 32)) (v_3234 : reg (bv 32)) => do
      v_6257 <- getRegister v_3234;
      v_6258 <- getRegister v_3233;
      v_6259 <- eval (bv_and v_6258 (expression.bv_nat 32 31));
      setRegister (lhs.of_reg v_3234) (bv_or v_6257 (extract (shl (expression.bv_nat 32 1) v_6259) 0 32));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_6257 v_6259) 31);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3219 : imm int) (v_3221 : Mem) => do
      v_10989 <- evaluateAddress v_3221;
      v_10990 <- eval (handleImmediateWithSignExtend v_3219 8 8);
      v_10994 <- eval (add v_10989 (concat (expression.bv_nat 59 0) (bv_and (extract v_10990 0 5) (expression.bv_nat 5 3))));
      v_10995 <- load v_10994 1;
      v_10998 <- eval (concat (expression.bv_nat 5 0) (bv_and (extract v_10990 5 8) (expression.bv_nat 3 7)));
      store v_10994 (bv_or v_10995 (extract (shl (expression.bv_nat 8 1) v_10998) 0 8)) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_10995 v_10998) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3224 : reg (bv 32)) (v_3225 : Mem) => do
      v_11010 <- evaluateAddress v_3225;
      v_11011 <- getRegister v_3224;
      v_11015 <- eval (add v_11010 (concat (expression.bv_nat 3 0) (extract (sext v_11011 64) 0 61)));
      v_11016 <- load v_11015 1;
      v_11018 <- eval (concat (expression.bv_nat 5 0) (extract v_11011 29 32));
      store v_11015 (bv_or v_11016 (extract (shl (expression.bv_nat 8 1) v_11018) 0 8)) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_11016 v_11018) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end
