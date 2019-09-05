def btrq1 : instruction :=
  definst "btrq" $ do
    pattern fun (v_3191 : imm int) (v_3194 : reg (bv 64)) => do
      v_6164 <- getRegister v_3194;
      v_6167 <- eval (sext (bv_and (handleImmediateWithSignExtend v_3191 8 8) (expression.bv_nat 8 63)) 64);
      setRegister (lhs.of_reg v_3194) (bv_and v_6164 (bv_xor (extract (shl (expression.bv_nat 64 1) v_6167) 0 64) (expression.bv_nat 64 18446744073709551615)));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_6164 v_6167) 63);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3198 : reg (bv 64)) (v_3199 : reg (bv 64)) => do
      v_6180 <- getRegister v_3199;
      v_6181 <- getRegister v_3198;
      v_6182 <- eval (bv_and v_6181 (expression.bv_nat 64 63));
      setRegister (lhs.of_reg v_3199) (bv_and v_6180 (bv_xor (extract (shl (expression.bv_nat 64 1) v_6182) 0 64) (expression.bv_nat 64 18446744073709551615)));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_6180 v_6182) 63);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3183 : imm int) (v_3185 : Mem) => do
      v_10904 <- evaluateAddress v_3185;
      v_10905 <- eval (handleImmediateWithSignExtend v_3183 8 8);
      v_10909 <- eval (add v_10904 (concat (expression.bv_nat 59 0) (bv_and (extract v_10905 0 5) (expression.bv_nat 5 7))));
      v_10910 <- load v_10909 1;
      v_10913 <- eval (concat (expression.bv_nat 5 0) (bv_and (extract v_10905 5 8) (expression.bv_nat 3 7)));
      store v_10909 (bv_and v_10910 (bv_xor (extract (shl (expression.bv_nat 8 1) v_10913) 0 8) (expression.bv_nat 8 255))) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_10910 v_10913) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3189 : reg (bv 64)) (v_3188 : Mem) => do
      v_10926 <- evaluateAddress v_3188;
      v_10927 <- getRegister v_3189;
      v_10930 <- eval (add v_10926 (concat (expression.bv_nat 3 0) (extract v_10927 0 61)));
      v_10931 <- load v_10930 1;
      v_10933 <- eval (concat (expression.bv_nat 5 0) (extract v_10927 61 64));
      store v_10930 (bv_and v_10931 (bv_xor (extract (shl (expression.bv_nat 8 1) v_10933) 0 8) (expression.bv_nat 8 255))) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_10931 v_10933) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end
