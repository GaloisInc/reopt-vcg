def bextrq1 : instruction :=
  definst "bextrq" $ do
    pattern fun (v_2995 : reg (bv 64)) (v_2996 : reg (bv 64)) (v_2997 : reg (bv 64)) => do
      v_5586 <- getRegister v_2996;
      v_5588 <- getRegister v_2995;
      v_5594 <- eval (concat (expression.bv_nat 504 0) (extract v_5588 48 56));
      v_5600 <- eval (bv_and (extract (lshr (concat (expression.bv_nat 448 0) v_5586) (concat (expression.bv_nat 504 0) (extract v_5588 56 64))) 448 512) (bv_xor (extract (extract (shl (lshr (expression.bv_nat 512 18446744073709551615) v_5594) v_5594) 0 512) 448 512) (expression.bv_nat 64 18446744073709551615)));
      setRegister (lhs.of_reg v_2997) v_5600;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf (zeroFlag v_5600);
      pure ()
    pat_end;
    pattern fun (v_2991 : reg (bv 64)) (v_2990 : Mem) (v_2992 : reg (bv 64)) => do
      v_9088 <- evaluateAddress v_2990;
      v_9089 <- load v_9088 8;
      v_9091 <- getRegister v_2991;
      v_9097 <- eval (concat (expression.bv_nat 504 0) (extract v_9091 48 56));
      v_9103 <- eval (bv_and (extract (lshr (concat (expression.bv_nat 448 0) v_9089) (concat (expression.bv_nat 504 0) (extract v_9091 56 64))) 448 512) (bv_xor (extract (extract (shl (lshr (expression.bv_nat 512 18446744073709551615) v_9097) v_9097) 0 512) 448 512) (expression.bv_nat 64 18446744073709551615)));
      setRegister (lhs.of_reg v_2992) v_9103;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf (zeroFlag v_9103);
      pure ()
    pat_end
