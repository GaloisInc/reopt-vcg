def mulss : instruction :=
  definst "mulss" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      v_3 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_2 96 128));
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 4;
      v_6 <- eval (bv_bitcast_to_fp float_class.fp32 v_5);
      setRegister (lhs.of_reg xmm_1) (concat (extract v_2 0 96) (fp_bitcast_to_bv (fp_mul v_3 v_6) 32));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      v_3 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_2 96 128));
      v_4 <- getRegister (lhs.of_reg xmm_0);
      v_5 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_4 96 128));
      setRegister (lhs.of_reg xmm_1) (concat (extract v_2 0 96) (fp_bitcast_to_bv (fp_mul v_3 v_5) 32));
      pure ()
    pat_end
