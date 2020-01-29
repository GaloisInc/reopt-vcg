def bextrl : instruction :=
  definst "bextrl" $ do
    pattern fun (r32_0 : reg (bv 32)) (mem_1 : Mem) (r32_2 : reg (bv 32)) => do
      v_3 <- evaluateAddress mem_1;
      v_4 <- load v_3 4;
      v_5 <- getRegister (lhs.of_reg r32_0);
      (v_6 : expression (bv 8)) <- eval (extract v_5 24 32);
      (v_7 : expression (bv 32)) <- eval (extract (lshr (concat (expression.bv_nat 480 0) v_4) (concat (expression.bv_nat 504 0) v_6)) 480 512);
      (v_8 : expression (bv 8)) <- eval (extract v_5 16 24);
      v_9 <- eval (concat (expression.bv_nat 504 0) v_8);
      (v_10 : expression (bv 512)) <- eval (extract (shl (lshr (expression.bv_nat 512 18446744073709551615) v_9) v_9) 0 512);
      (v_11 : expression (bv 32)) <- eval (extract v_10 480 512);
      v_12 <- eval (bv_and v_7 (bv_xor v_11 (expression.bv_nat 32 4294967295)));
      setRegister (lhs.of_reg r32_2) v_12;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf (zeroFlag v_12);
      pure ()
    pat_end;
    pattern fun (r32_0 : reg (bv 32)) (r32_1 : reg (bv 32)) (r32_2 : reg (bv 32)) => do
      v_3 <- getRegister (lhs.of_reg r32_1);
      v_4 <- getRegister (lhs.of_reg r32_0);
      (v_5 : expression (bv 8)) <- eval (extract v_4 24 32);
      (v_6 : expression (bv 32)) <- eval (extract (lshr (concat (expression.bv_nat 480 0) v_3) (concat (expression.bv_nat 504 0) v_5)) 480 512);
      (v_7 : expression (bv 8)) <- eval (extract v_4 16 24);
      v_8 <- eval (concat (expression.bv_nat 504 0) v_7);
      (v_9 : expression (bv 512)) <- eval (extract (shl (lshr (expression.bv_nat 512 18446744073709551615) v_8) v_8) 0 512);
      (v_10 : expression (bv 32)) <- eval (extract v_9 480 512);
      v_11 <- eval (bv_and v_6 (bv_xor v_10 (expression.bv_nat 32 4294967295)));
      setRegister (lhs.of_reg r32_2) v_11;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf (zeroFlag v_11);
      pure ()
    pat_end
