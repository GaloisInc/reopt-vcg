def bextrl : instruction :=
  definst "bextrl" $ do
    instr_pat $ fun (r32_0 : reg (bv 32)) (mem_1 : Mem) (r32_2 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_1;
      let v_4 <- load v_3 4;
      let v_5 <- eval (concat (expression.bv_nat 480 0) v_4);
      let v_6 <- getRegister (lhs.of_reg r32_0);
      let (v_7 : expression (bv 8)) <- eval (extract v_6 24 32);
      let v_8 <- eval (concat (expression.bv_nat 504 0) v_7);
      let (v_9 : expression (bv 32)) <- eval (extract (lshr v_5 v_8) 480 512);
      let (v_10 : expression (bv 8)) <- eval (extract v_6 16 24);
      let v_11 <- eval (concat (expression.bv_nat 504 0) v_10);
      let (v_12 : expression (bv 512)) <- eval (extract (shl (lshr (expression.bv_nat 512 18446744073709551615) v_11) v_11) 0 512);
      let (v_13 : expression (bv 32)) <- eval (extract v_12 480 512);
      let v_14 <- eval (bv_and v_9 (bv_xor v_13 (expression.bv_nat 32 4294967295)));
      setRegister (lhs.of_reg r32_2) v_14;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf (zeroFlag v_14);
      pure ()
     action;
    instr_pat $ fun (r32_0 : reg (bv 32)) (r32_1 : reg (bv 32)) (r32_2 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg r32_1);
      let v_4 <- eval (concat (expression.bv_nat 480 0) v_3);
      let v_5 <- getRegister (lhs.of_reg r32_0);
      let (v_6 : expression (bv 8)) <- eval (extract v_5 24 32);
      let v_7 <- eval (concat (expression.bv_nat 504 0) v_6);
      let (v_8 : expression (bv 32)) <- eval (extract (lshr v_4 v_7) 480 512);
      let (v_9 : expression (bv 8)) <- eval (extract v_5 16 24);
      let v_10 <- eval (concat (expression.bv_nat 504 0) v_9);
      let (v_11 : expression (bv 512)) <- eval (extract (shl (lshr (expression.bv_nat 512 18446744073709551615) v_10) v_10) 0 512);
      let (v_12 : expression (bv 32)) <- eval (extract v_11 480 512);
      let v_13 <- eval (bv_and v_8 (bv_xor v_12 (expression.bv_nat 32 4294967295)));
      setRegister (lhs.of_reg r32_2) v_13;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf (zeroFlag v_13);
      pure ()
     action
