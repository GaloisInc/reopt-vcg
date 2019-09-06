def vpsrlw1 : instruction :=
  definst "vpsrlw" $ do
    pattern fun (v_3497 : imm int) (v_3499 : reg (bv 128)) (v_3500 : reg (bv 128)) => do
      v_8893 <- eval (handleImmediateWithSignExtend v_3497 8 8);
      v_8896 <- getRegister v_3499;
      v_8898 <- eval (concat (expression.bv_nat 8 0) v_8893);
      setRegister (lhs.of_reg v_3500) (mux (ugt (concat (expression.bv_nat 56 0) v_8893) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (lshr (extract v_8896 0 16) v_8898) (concat (lshr (extract v_8896 16 32) v_8898) (concat (lshr (extract v_8896 32 48) v_8898) (concat (lshr (extract v_8896 48 64) v_8898) (concat (lshr (extract v_8896 64 80) v_8898) (concat (lshr (extract v_8896 80 96) v_8898) (concat (lshr (extract v_8896 96 112) v_8898) (lshr (extract v_8896 112 128) v_8898)))))))));
      pure ()
    pat_end;
    pattern fun (v_3509 : reg (bv 128)) (v_3510 : reg (bv 128)) (v_3511 : reg (bv 128)) => do
      v_8928 <- getRegister v_3509;
      v_8931 <- getRegister v_3510;
      v_8933 <- eval (extract v_8928 112 128);
      setRegister (lhs.of_reg v_3511) (mux (ugt (extract v_8928 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (lshr (extract v_8931 0 16) v_8933) (concat (lshr (extract v_8931 16 32) v_8933) (concat (lshr (extract v_8931 32 48) v_8933) (concat (lshr (extract v_8931 48 64) v_8933) (concat (lshr (extract v_8931 64 80) v_8933) (concat (lshr (extract v_8931 80 96) v_8933) (concat (lshr (extract v_8931 96 112) v_8933) (lshr (extract v_8931 112 128) v_8933)))))))));
      pure ()
    pat_end;
    pattern fun (v_3514 : imm int) (v_3516 : reg (bv 256)) (v_3517 : reg (bv 256)) => do
      v_8958 <- eval (handleImmediateWithSignExtend v_3514 8 8);
      v_8961 <- getRegister v_3516;
      v_8963 <- eval (concat (expression.bv_nat 8 0) v_8958);
      setRegister (lhs.of_reg v_3517) (mux (ugt (concat (expression.bv_nat 56 0) v_8958) (expression.bv_nat 64 15)) (expression.bv_nat 256 0) (concat (lshr (extract v_8961 0 16) v_8963) (concat (lshr (extract v_8961 16 32) v_8963) (concat (lshr (extract v_8961 32 48) v_8963) (concat (lshr (extract v_8961 48 64) v_8963) (concat (lshr (extract v_8961 64 80) v_8963) (concat (lshr (extract v_8961 80 96) v_8963) (concat (lshr (extract v_8961 96 112) v_8963) (concat (lshr (extract v_8961 112 128) v_8963) (concat (lshr (extract v_8961 128 144) v_8963) (concat (lshr (extract v_8961 144 160) v_8963) (concat (lshr (extract v_8961 160 176) v_8963) (concat (lshr (extract v_8961 176 192) v_8963) (concat (lshr (extract v_8961 192 208) v_8963) (concat (lshr (extract v_8961 208 224) v_8963) (concat (lshr (extract v_8961 224 240) v_8963) (lshr (extract v_8961 240 256) v_8963)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3528 : reg (bv 128)) (v_3526 : reg (bv 256)) (v_3527 : reg (bv 256)) => do
      v_9017 <- getRegister v_3528;
      v_9020 <- getRegister v_3526;
      v_9022 <- eval (extract v_9017 112 128);
      setRegister (lhs.of_reg v_3527) (mux (ugt (extract v_9017 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 256 0) (concat (lshr (extract v_9020 0 16) v_9022) (concat (lshr (extract v_9020 16 32) v_9022) (concat (lshr (extract v_9020 32 48) v_9022) (concat (lshr (extract v_9020 48 64) v_9022) (concat (lshr (extract v_9020 64 80) v_9022) (concat (lshr (extract v_9020 80 96) v_9022) (concat (lshr (extract v_9020 96 112) v_9022) (concat (lshr (extract v_9020 112 128) v_9022) (concat (lshr (extract v_9020 128 144) v_9022) (concat (lshr (extract v_9020 144 160) v_9022) (concat (lshr (extract v_9020 160 176) v_9022) (concat (lshr (extract v_9020 176 192) v_9022) (concat (lshr (extract v_9020 192 208) v_9022) (concat (lshr (extract v_9020 208 224) v_9022) (concat (lshr (extract v_9020 224 240) v_9022) (lshr (extract v_9020 240 256) v_9022)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3503 : Mem) (v_3504 : reg (bv 128)) (v_3505 : reg (bv 128)) => do
      v_14619 <- evaluateAddress v_3503;
      v_14620 <- load v_14619 16;
      v_14623 <- getRegister v_3504;
      v_14625 <- eval (extract v_14620 112 128);
      setRegister (lhs.of_reg v_3505) (mux (ugt (extract v_14620 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (lshr (extract v_14623 0 16) v_14625) (concat (lshr (extract v_14623 16 32) v_14625) (concat (lshr (extract v_14623 32 48) v_14625) (concat (lshr (extract v_14623 48 64) v_14625) (concat (lshr (extract v_14623 64 80) v_14625) (concat (lshr (extract v_14623 80 96) v_14625) (concat (lshr (extract v_14623 96 112) v_14625) (lshr (extract v_14623 112 128) v_14625)))))))));
      pure ()
    pat_end;
    pattern fun (v_3520 : Mem) (v_3521 : reg (bv 256)) (v_3522 : reg (bv 256)) => do
      v_14650 <- evaluateAddress v_3520;
      v_14651 <- load v_14650 16;
      v_14654 <- getRegister v_3521;
      v_14656 <- eval (extract v_14651 112 128);
      setRegister (lhs.of_reg v_3522) (mux (ugt (extract v_14651 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 256 0) (concat (lshr (extract v_14654 0 16) v_14656) (concat (lshr (extract v_14654 16 32) v_14656) (concat (lshr (extract v_14654 32 48) v_14656) (concat (lshr (extract v_14654 48 64) v_14656) (concat (lshr (extract v_14654 64 80) v_14656) (concat (lshr (extract v_14654 80 96) v_14656) (concat (lshr (extract v_14654 96 112) v_14656) (concat (lshr (extract v_14654 112 128) v_14656) (concat (lshr (extract v_14654 128 144) v_14656) (concat (lshr (extract v_14654 144 160) v_14656) (concat (lshr (extract v_14654 160 176) v_14656) (concat (lshr (extract v_14654 176 192) v_14656) (concat (lshr (extract v_14654 192 208) v_14656) (concat (lshr (extract v_14654 208 224) v_14656) (concat (lshr (extract v_14654 224 240) v_14656) (lshr (extract v_14654 240 256) v_14656)))))))))))))))));
      pure ()
    pat_end
