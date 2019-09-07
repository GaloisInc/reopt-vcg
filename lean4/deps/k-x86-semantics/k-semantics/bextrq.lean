def bextrq1 : instruction :=
  definst "bextrq" $ do
    pattern fun (r64_0 : reg (bv 64)) (mem_1 : Mem) (r64_2 : reg (bv 64)) => do
      v_3 <- evaluateAddress mem_1;
      v_4 <- load v_3 8;
      v_5 <- getRegister r64_0;
      v_6 <- eval (concat (expression.bv_nat 504 0) (extract v_5 48 56));
      v_7 <- eval (bv_and (extract (lshr (concat (expression.bv_nat 448 0) v_4) (concat (expression.bv_nat 504 0) (extract v_5 56 64))) 448 512) (bv_xor (extract (extract (shl (lshr (expression.bv_nat 512 18446744073709551615) v_6) v_6) 0 512) 448 512) (expression.bv_nat 64 18446744073709551615)));
      setRegister (lhs.of_reg r64_2) v_7;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf (zeroFlag v_7);
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) (r64_1 : reg (bv 64)) (r64_2 : reg (bv 64)) => do
      v_3 <- getRegister r64_1;
      v_4 <- getRegister r64_0;
      v_5 <- eval (concat (expression.bv_nat 504 0) (extract v_4 48 56));
      v_6 <- eval (bv_and (extract (lshr (concat (expression.bv_nat 448 0) v_3) (concat (expression.bv_nat 504 0) (extract v_4 56 64))) 448 512) (bv_xor (extract (extract (shl (lshr (expression.bv_nat 512 18446744073709551615) v_5) v_5) 0 512) 448 512) (expression.bv_nat 64 18446744073709551615)));
      setRegister (lhs.of_reg r64_2) v_6;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf (zeroFlag v_6);
      pure ()
    pat_end
