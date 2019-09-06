def psrlw1 : instruction :=
  definst "psrlw" $ do
    pattern fun (v_3154 : imm int) (v_3155 : reg (bv 128)) => do
      v_7905 <- eval (handleImmediateWithSignExtend v_3154 8 8);
      v_7908 <- getRegister v_3155;
      v_7910 <- eval (concat (expression.bv_nat 8 0) v_7905);
      setRegister (lhs.of_reg v_3155) (mux (ugt (concat (expression.bv_nat 56 0) v_7905) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (lshr (extract v_7908 0 16) v_7910) (concat (lshr (extract v_7908 16 32) v_7910) (concat (lshr (extract v_7908 32 48) v_7910) (concat (lshr (extract v_7908 48 64) v_7910) (concat (lshr (extract v_7908 64 80) v_7910) (concat (lshr (extract v_7908 80 96) v_7910) (concat (lshr (extract v_7908 96 112) v_7910) (lshr (extract v_7908 112 128) v_7910)))))))));
      pure ()
    pat_end;
    pattern fun (v_3163 : reg (bv 128)) (v_3164 : reg (bv 128)) => do
      v_7939 <- getRegister v_3163;
      v_7942 <- getRegister v_3164;
      v_7944 <- eval (extract v_7939 112 128);
      setRegister (lhs.of_reg v_3164) (mux (ugt (extract v_7939 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (lshr (extract v_7942 0 16) v_7944) (concat (lshr (extract v_7942 16 32) v_7944) (concat (lshr (extract v_7942 32 48) v_7944) (concat (lshr (extract v_7942 48 64) v_7944) (concat (lshr (extract v_7942 64 80) v_7944) (concat (lshr (extract v_7942 80 96) v_7944) (concat (lshr (extract v_7942 96 112) v_7944) (lshr (extract v_7942 112 128) v_7944)))))))));
      pure ()
    pat_end;
    pattern fun (v_3159 : Mem) (v_3160 : reg (bv 128)) => do
      v_14372 <- evaluateAddress v_3159;
      v_14373 <- load v_14372 16;
      v_14376 <- getRegister v_3160;
      v_14378 <- eval (extract v_14373 112 128);
      setRegister (lhs.of_reg v_3160) (mux (ugt (extract v_14373 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (lshr (extract v_14376 0 16) v_14378) (concat (lshr (extract v_14376 16 32) v_14378) (concat (lshr (extract v_14376 32 48) v_14378) (concat (lshr (extract v_14376 48 64) v_14378) (concat (lshr (extract v_14376 64 80) v_14378) (concat (lshr (extract v_14376 80 96) v_14378) (concat (lshr (extract v_14376 96 112) v_14378) (lshr (extract v_14376 112 128) v_14378)))))))));
      pure ()
    pat_end
