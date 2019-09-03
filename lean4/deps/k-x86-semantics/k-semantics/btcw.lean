def btcw1 : instruction :=
  definst "btcw" $ do
    pattern fun (v_3055 : imm int) (v_3058 : reg (bv 16)) => do
      v_6124 <- getRegister v_3058;
      v_6129 <- eval (uvalueMInt (mi 16 (svalueMInt (bv_and (handleImmediateWithSignExtend v_3055 8 8) (expression.bv_nat 8 15)))));
      setRegister (lhs.of_reg v_3058) (bv_xor v_6124 (extract (shl (expression.bv_nat 16 1) v_6129) 0 16));
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6124 v_6129) 15 16);
      pure ()
    pat_end;
    pattern fun (v_3062 : reg (bv 16)) (v_3063 : reg (bv 16)) => do
      v_6141 <- getRegister v_3063;
      v_6142 <- getRegister v_3062;
      v_6146 <- eval (uvalueMInt (mi 16 (svalueMInt (bv_and v_6142 (expression.bv_nat 16 15)))));
      setRegister (lhs.of_reg v_3063) (bv_xor v_6141 (extract (shl (expression.bv_nat 16 1) v_6146) 0 16));
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6141 v_6146) 15 16);
      pure ()
    pat_end;
    pattern fun (v_3047 : imm int) (v_3049 : Mem) => do
      v_11136 <- evaluateAddress v_3049;
      v_11137 <- eval (handleImmediateWithSignExtend v_3047 8 8);
      v_11141 <- eval (add v_11136 (concat (expression.bv_nat 59 0) (bv_and (extract v_11137 0 5) (expression.bv_nat 5 1))));
      v_11142 <- load v_11141 1;
      v_11146 <- eval (uvalueMInt (concat (expression.bv_nat 5 0) (bv_and (extract v_11137 5 8) (expression.bv_nat 3 7))));
      store v_11141 (bv_xor v_11142 (extract (shl (expression.bv_nat 8 1) v_11146) 0 8)) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_11142 v_11146) 7 8);
      pure ()
    pat_end;
    pattern fun (v_3053 : reg (bv 16)) (v_3052 : Mem) => do
      v_11158 <- evaluateAddress v_3052;
      v_11159 <- getRegister v_3053;
      v_11164 <- eval (add v_11158 (concat (expression.bv_nat 3 0) (extract (mi 64 (svalueMInt v_11159)) 0 61)));
      v_11165 <- load v_11164 1;
      v_11168 <- eval (uvalueMInt (concat (expression.bv_nat 5 0) (extract v_11159 13 16)));
      store v_11164 (bv_xor v_11165 (extract (shl (expression.bv_nat 8 1) v_11168) 0 8)) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_11165 v_11168) 7 8);
      pure ()
    pat_end
