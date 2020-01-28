def cvtsd2ss : instruction :=
  definst "cvtsd2ss" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 8;
      v_5 <- eval (bv_bitcast_to_fp float_class.fp64 v_4);
      setRegister (lhs.of_reg xmm_1) (concat (extract v_2 0 96) (fp_bitcast_to_bv (fp_round v_5 24 8) 32));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      v_3 <- getRegister (lhs.of_reg xmm_0);
      v_4 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_3 64 128));
      setRegister (lhs.of_reg xmm_1) (concat (extract v_2 0 96) (fp_bitcast_to_bv (fp_round v_4 24 8) 32));
      pure ()
    pat_end
