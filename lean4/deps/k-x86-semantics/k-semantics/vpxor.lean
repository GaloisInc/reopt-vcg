def vpxor1 : instruction :=
  definst "vpxor" $ do
    pattern fun (v_2814 : Mem) (v_2815 : reg (bv 128)) (v_2816 : reg (bv 128)) => do
      v_12567 <- getRegister v_2815;
      v_12568 <- evaluateAddress v_2814;
      v_12569 <- load v_12568 16;
      setRegister (lhs.of_reg v_2816) (bv_xor v_12567 v_12569);
      pure ()
    pat_end;
    pattern fun (v_2825 : Mem) (v_2826 : reg (bv 256)) (v_2827 : reg (bv 256)) => do
      v_12572 <- getRegister v_2826;
      v_12573 <- evaluateAddress v_2825;
      v_12574 <- load v_12573 32;
      setRegister (lhs.of_reg v_2827) (bv_xor v_12572 v_12574);
      pure ()
    pat_end
