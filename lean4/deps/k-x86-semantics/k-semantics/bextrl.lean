def bextrl : instruction :=
  definst "bextrl" $ do
    pattern fun (r32_0 : reg (bv 32)) (mem_1 : Mem) (r32_2 : reg (bv 32)) => do
      v_3 <- evaluateAddress mem_1;
      v_4 <- load v_3 4;
      v_5 <- getRegister (lhs.of_reg r32_0);
      v_6 <- eval (concat (expression.bv_nat 504 0) (extract v_5 16 24));
      v_7 <- eval (bv_and (extract (lshr (concat (expression.bv_nat 480 0) v_4) (concat (expression.bv_nat 504 0) (extract v_5 24 32))) 480 512) (bv_xor (extract (extract (shl (lshr (expression.bv_nat 512 18446744073709551615) v_6) v_6) 0 512) 480 512) (expression.bv_nat 32 4294967295)));
      setRegister (lhs.of_reg r32_2) v_7;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf (zeroFlag v_7);
      pure ()
    pat_end;
    pattern fun (r32_0 : reg (bv 32)) (r32_1 : reg (bv 32)) (r32_2 : reg (bv 32)) => do
      v_3 <- getRegister (lhs.of_reg r32_1);
      v_4 <- getRegister (lhs.of_reg r32_0);
      v_5 <- eval (concat (expression.bv_nat 504 0) (extract v_4 16 24));
      v_6 <- eval (bv_and (extract (lshr (concat (expression.bv_nat 480 0) v_3) (concat (expression.bv_nat 504 0) (extract v_4 24 32))) 480 512) (bv_xor (extract (extract (shl (lshr (expression.bv_nat 512 18446744073709551615) v_5) v_5) 0 512) 480 512) (expression.bv_nat 32 4294967295)));
      setRegister (lhs.of_reg r32_2) v_6;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf (zeroFlag v_6);
      pure ()
    pat_end
