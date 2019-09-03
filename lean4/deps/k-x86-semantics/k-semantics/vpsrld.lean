def vpsrld1 : instruction :=
  definst "vpsrld" $ do
    pattern fun (v_3284 : imm int) (v_3282 : reg (bv 128)) (v_3283 : reg (bv 128)) => do
      v_9221 <- eval (handleImmediateWithSignExtend v_3284 8 8);
      v_9224 <- getRegister v_3282;
      v_9227 <- eval (uvalueMInt (concat (expression.bv_nat 24 0) v_9221));
      setRegister (lhs.of_reg v_3283) (mux (ugt (concat (expression.bv_nat 56 0) v_9221) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (lshr (extract v_9224 0 32) v_9227) (concat (lshr (extract v_9224 32 64) v_9227) (concat (lshr (extract v_9224 64 96) v_9227) (lshr (extract v_9224 96 128) v_9227)))));
      pure ()
    pat_end;
    pattern fun (v_3293 : reg (bv 128)) (v_3294 : reg (bv 128)) (v_3295 : reg (bv 128)) => do
      v_9245 <- getRegister v_3293;
      v_9248 <- getRegister v_3294;
      v_9251 <- eval (uvalueMInt (extract v_9245 96 128));
      setRegister (lhs.of_reg v_3295) (mux (ugt (extract v_9245 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (lshr (extract v_9248 0 32) v_9251) (concat (lshr (extract v_9248 32 64) v_9251) (concat (lshr (extract v_9248 64 96) v_9251) (lshr (extract v_9248 96 128) v_9251)))));
      pure ()
    pat_end;
    pattern fun (v_3299 : imm int) (v_3300 : reg (bv 256)) (v_3301 : reg (bv 256)) => do
      v_9264 <- eval (handleImmediateWithSignExtend v_3299 8 8);
      v_9267 <- getRegister v_3300;
      v_9270 <- eval (uvalueMInt (concat (expression.bv_nat 24 0) v_9264));
      setRegister (lhs.of_reg v_3301) (mux (ugt (concat (expression.bv_nat 56 0) v_9264) (expression.bv_nat 64 31)) (expression.bv_nat 256 0) (concat (lshr (extract v_9267 0 32) v_9270) (concat (lshr (extract v_9267 32 64) v_9270) (concat (lshr (extract v_9267 64 96) v_9270) (concat (lshr (extract v_9267 96 128) v_9270) (concat (lshr (extract v_9267 128 160) v_9270) (concat (lshr (extract v_9267 160 192) v_9270) (concat (lshr (extract v_9267 192 224) v_9270) (lshr (extract v_9267 224 256) v_9270)))))))));
      pure ()
    pat_end;
    pattern fun (v_3310 : reg (bv 128)) (v_3311 : reg (bv 256)) (v_3312 : reg (bv 256)) => do
      v_9300 <- getRegister v_3310;
      v_9303 <- getRegister v_3311;
      v_9306 <- eval (uvalueMInt (extract v_9300 96 128));
      setRegister (lhs.of_reg v_3312) (mux (ugt (extract v_9300 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 256 0) (concat (lshr (extract v_9303 0 32) v_9306) (concat (lshr (extract v_9303 32 64) v_9306) (concat (lshr (extract v_9303 64 96) v_9306) (concat (lshr (extract v_9303 96 128) v_9306) (concat (lshr (extract v_9303 128 160) v_9306) (concat (lshr (extract v_9303 160 192) v_9306) (concat (lshr (extract v_9303 192 224) v_9306) (lshr (extract v_9303 224 256) v_9306)))))))));
      pure ()
    pat_end;
    pattern fun (v_3290 : Mem) (v_3288 : reg (bv 128)) (v_3289 : reg (bv 128)) => do
      v_15657 <- evaluateAddress v_3290;
      v_15658 <- load v_15657 16;
      v_15661 <- getRegister v_3288;
      v_15664 <- eval (uvalueMInt (extract v_15658 96 128));
      setRegister (lhs.of_reg v_3289) (mux (ugt (extract v_15658 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (lshr (extract v_15661 0 32) v_15664) (concat (lshr (extract v_15661 32 64) v_15664) (concat (lshr (extract v_15661 64 96) v_15664) (lshr (extract v_15661 96 128) v_15664)))));
      pure ()
    pat_end;
    pattern fun (v_3305 : Mem) (v_3306 : reg (bv 256)) (v_3307 : reg (bv 256)) => do
      v_15677 <- evaluateAddress v_3305;
      v_15678 <- load v_15677 16;
      v_15681 <- getRegister v_3306;
      v_15684 <- eval (uvalueMInt (extract v_15678 96 128));
      setRegister (lhs.of_reg v_3307) (mux (ugt (extract v_15678 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 256 0) (concat (lshr (extract v_15681 0 32) v_15684) (concat (lshr (extract v_15681 32 64) v_15684) (concat (lshr (extract v_15681 64 96) v_15684) (concat (lshr (extract v_15681 96 128) v_15684) (concat (lshr (extract v_15681 128 160) v_15684) (concat (lshr (extract v_15681 160 192) v_15684) (concat (lshr (extract v_15681 192 224) v_15684) (lshr (extract v_15681 224 256) v_15684)))))))));
      pure ()
    pat_end
