def bextrq : instruction :=
  definst "bextrq" $ do
    instr_pat $ fun (r64_0 : reg (bv 64)) (mem_1 : Mem) (r64_2 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_1;
      let v_4 <- load v_3 8;
      let v_5 <- eval (concat (expression.bv_nat 448 0) v_4);
      let v_6 <- getRegister (lhs.of_reg r64_0);
      let (v_7 : expression (bv 8)) <- eval (extract v_6 56 64);
      let v_8 <- eval (concat (expression.bv_nat 504 0) v_7);
      let (v_9 : expression (bv 64)) <- eval (extract (lshr v_5 v_8) 448 512);
      let (v_10 : expression (bv 8)) <- eval (extract v_6 48 56);
      let v_11 <- eval (concat (expression.bv_nat 504 0) v_10);
      let (v_12 : expression (bv 512)) <- eval (extract (shl (lshr (expression.bv_nat 512 18446744073709551615) v_11) v_11) 0 512);
      let (v_13 : expression (bv 64)) <- eval (extract v_12 448 512);
      let v_14 <- eval (bv_and v_9 (bv_xor v_13 (expression.bv_nat 64 18446744073709551615)));
      setRegister (lhs.of_reg r64_2) v_14;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf (zeroFlag v_14);
      pure ()
     action;
    instr_pat $ fun (r64_0 : reg (bv 64)) (r64_1 : reg (bv 64)) (r64_2 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg r64_1);
      let v_4 <- eval (concat (expression.bv_nat 448 0) v_3);
      let v_5 <- getRegister (lhs.of_reg r64_0);
      let (v_6 : expression (bv 8)) <- eval (extract v_5 56 64);
      let v_7 <- eval (concat (expression.bv_nat 504 0) v_6);
      let (v_8 : expression (bv 64)) <- eval (extract (lshr v_4 v_7) 448 512);
      let (v_9 : expression (bv 8)) <- eval (extract v_5 48 56);
      let v_10 <- eval (concat (expression.bv_nat 504 0) v_9);
      let (v_11 : expression (bv 512)) <- eval (extract (shl (lshr (expression.bv_nat 512 18446744073709551615) v_10) v_10) 0 512);
      let (v_12 : expression (bv 64)) <- eval (extract v_11 448 512);
      let v_13 <- eval (bv_and v_8 (bv_xor v_12 (expression.bv_nat 64 18446744073709551615)));
      setRegister (lhs.of_reg r64_2) v_13;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf (zeroFlag v_13);
      pure ()
     action
