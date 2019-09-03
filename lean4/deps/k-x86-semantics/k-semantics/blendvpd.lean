def blendvpd1 : instruction :=
  definst "blendvpd" $ do
    pattern fun xmm0 (v_2950 : reg (bv 128)) (v_2951 : reg (bv 128)) => do
      v_5993 <- getRegister ymm0;
      v_5996 <- getRegister v_2951;
      v_5998 <- getRegister v_2950;
      setRegister (lhs.of_reg v_2951) (concat (mux (eq (extract v_5993 128 129) (expression.bv_nat 1 0)) (extract v_5996 0 64) (extract v_5998 0 64)) (mux (eq (extract v_5993 192 193) (expression.bv_nat 1 0)) (extract v_5996 64 128) (extract v_5998 64 128)));
      pure ()
    pat_end;
    pattern fun xmm0 (v_2945 : Mem) (v_2946 : reg (bv 128)) => do
      v_9835 <- getRegister ymm0;
      v_9838 <- getRegister v_2946;
      v_9840 <- evaluateAddress v_2945;
      v_9841 <- load v_9840 16;
      setRegister (lhs.of_reg v_2946) (concat (mux (eq (extract v_9835 128 129) (expression.bv_nat 1 0)) (extract v_9838 0 64) (extract v_9841 0 64)) (mux (eq (extract v_9835 192 193) (expression.bv_nat 1 0)) (extract v_9838 64 128) (extract v_9841 64 128)));
      pure ()
    pat_end
