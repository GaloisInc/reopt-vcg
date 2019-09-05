def psrad1 : instruction :=
  definst "psrad" $ do
    pattern fun (v_3066 : imm int) (v_3065 : reg (bv 128)) => do
      v_7699 <- getRegister v_3065;
      v_7701 <- eval (handleImmediateWithSignExtend v_3066 8 8);
      v_7705 <- eval (mux (ugt (concat (expression.bv_nat 56 0) v_7701) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (concat (expression.bv_nat 24 0) v_7701));
      setRegister (lhs.of_reg v_3065) (concat (ashr (extract v_7699 0 32) v_7705) (concat (ashr (extract v_7699 32 64) v_7705) (concat (ashr (extract v_7699 64 96) v_7705) (ashr (extract v_7699 96 128) v_7705))));
      pure ()
    pat_end;
    pattern fun (v_3074 : reg (bv 128)) (v_3075 : reg (bv 128)) => do
      v_7721 <- getRegister v_3075;
      v_7723 <- getRegister v_3074;
      v_7727 <- eval (mux (ugt (extract v_7723 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (extract v_7723 96 128));
      setRegister (lhs.of_reg v_3075) (concat (ashr (extract v_7721 0 32) v_7727) (concat (ashr (extract v_7721 32 64) v_7727) (concat (ashr (extract v_7721 64 96) v_7727) (ashr (extract v_7721 96 128) v_7727))));
      pure ()
    pat_end;
    pattern fun (v_3071 : Mem) (v_3070 : reg (bv 128)) => do
      v_14315 <- getRegister v_3070;
      v_14317 <- evaluateAddress v_3071;
      v_14318 <- load v_14317 16;
      v_14322 <- eval (mux (ugt (extract v_14318 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (extract v_14318 96 128));
      setRegister (lhs.of_reg v_3070) (concat (ashr (extract v_14315 0 32) v_14322) (concat (ashr (extract v_14315 32 64) v_14322) (concat (ashr (extract v_14315 64 96) v_14322) (ashr (extract v_14315 96 128) v_14322))));
      pure ()
    pat_end
