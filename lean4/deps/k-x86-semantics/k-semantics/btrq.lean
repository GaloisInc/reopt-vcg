def btrq1 : instruction :=
  definst "btrq" $ do
    pattern fun (v_3127 : imm int) (v_3130 : reg (bv 64)) => do
      v_6282 <- getRegister v_3130;
      v_6287 <- eval (uvalueMInt (mi 64 (svalueMInt (bv_and (handleImmediateWithSignExtend v_3127 8 8) (expression.bv_nat 8 63)))));
      v_6291 <- eval (extract (shl (expression.bv_nat 64 1) v_6287) 0 64);
      setRegister (lhs.of_reg v_3130) (bv_and v_6282 (bv_xor v_6291 (mi (bitwidthMInt v_6291) -1)));
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6282 v_6287) 63 64);
      pure ()
    pat_end;
    pattern fun (v_3134 : reg (bv 64)) (v_3135 : reg (bv 64)) => do
      v_6302 <- getRegister v_3135;
      v_6303 <- getRegister v_3134;
      v_6307 <- eval (uvalueMInt (mi 64 (svalueMInt (bv_and v_6303 (expression.bv_nat 64 63)))));
      v_6311 <- eval (extract (shl (expression.bv_nat 64 1) v_6307) 0 64);
      setRegister (lhs.of_reg v_3135) (bv_and v_6302 (bv_xor v_6311 (mi (bitwidthMInt v_6311) -1)));
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6302 v_6307) 63 64);
      pure ()
    pat_end;
    pattern fun (v_3119 : imm int) (v_3121 : Mem) => do
      v_11230 <- evaluateAddress v_3121;
      v_11231 <- eval (handleImmediateWithSignExtend v_3119 8 8);
      v_11235 <- eval (add v_11230 (concat (expression.bv_nat 59 0) (bv_and (extract v_11231 0 5) (expression.bv_nat 5 7))));
      v_11236 <- load v_11235 1;
      v_11240 <- eval (uvalueMInt (concat (expression.bv_nat 5 0) (bv_and (extract v_11231 5 8) (expression.bv_nat 3 7))));
      v_11242 <- eval (extract (shl (expression.bv_nat 8 1) v_11240) 0 8);
      store v_11235 (bv_and v_11236 (bv_xor v_11242 (mi (bitwidthMInt v_11242) -1))) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_11236 v_11240) 7 8);
      pure ()
    pat_end;
    pattern fun (v_3125 : reg (bv 64)) (v_3124 : Mem) => do
      v_11255 <- evaluateAddress v_3124;
      v_11256 <- getRegister v_3125;
      v_11259 <- eval (add v_11255 (concat (expression.bv_nat 3 0) (extract v_11256 0 61)));
      v_11260 <- load v_11259 1;
      v_11263 <- eval (uvalueMInt (concat (expression.bv_nat 5 0) (extract v_11256 61 64)));
      v_11265 <- eval (extract (shl (expression.bv_nat 8 1) v_11263) 0 8);
      store v_11259 (bv_and v_11260 (bv_xor v_11265 (mi (bitwidthMInt v_11265) -1))) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_11260 v_11263) 7 8);
      pure ()
    pat_end
