def cvtpi2pd : instruction :=
  definst "cvtpi2pd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 8;
      (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      (v_5 : expression (bv 32)) <- eval (extract v_3 32 64);
      setRegister (lhs.of_reg xmm_1) (concat (fp_bitcast_to_bv (Int2Float (svalueMInt v_4) 53 11) 64) (fp_bitcast_to_bv (Int2Float (svalueMInt v_5) 53 11) 64));
      pure ()
    pat_end