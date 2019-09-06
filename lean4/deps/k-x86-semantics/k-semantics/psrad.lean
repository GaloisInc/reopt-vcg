def psrad1 : instruction :=
  definst "psrad" $ do
    pattern fun (v_3093 : imm int) (v_3094 : reg (bv 128)) => do
      v_7726 <- getRegister v_3094;
      v_7728 <- eval (handleImmediateWithSignExtend v_3093 8 8);
      v_7732 <- eval (mux (ugt (concat (expression.bv_nat 56 0) v_7728) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (concat (expression.bv_nat 24 0) v_7728));
      setRegister (lhs.of_reg v_3094) (concat (ashr (extract v_7726 0 32) v_7732) (concat (ashr (extract v_7726 32 64) v_7732) (concat (ashr (extract v_7726 64 96) v_7732) (ashr (extract v_7726 96 128) v_7732))));
      pure ()
    pat_end;
    pattern fun (v_3102 : reg (bv 128)) (v_3103 : reg (bv 128)) => do
      v_7748 <- getRegister v_3103;
      v_7750 <- getRegister v_3102;
      v_7754 <- eval (mux (ugt (extract v_7750 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (extract v_7750 96 128));
      setRegister (lhs.of_reg v_3103) (concat (ashr (extract v_7748 0 32) v_7754) (concat (ashr (extract v_7748 32 64) v_7754) (concat (ashr (extract v_7748 64 96) v_7754) (ashr (extract v_7748 96 128) v_7754))));
      pure ()
    pat_end;
    pattern fun (v_3098 : Mem) (v_3099 : reg (bv 128)) => do
      v_14291 <- getRegister v_3099;
      v_14293 <- evaluateAddress v_3098;
      v_14294 <- load v_14293 16;
      v_14298 <- eval (mux (ugt (extract v_14294 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (extract v_14294 96 128));
      setRegister (lhs.of_reg v_3099) (concat (ashr (extract v_14291 0 32) v_14298) (concat (ashr (extract v_14291 32 64) v_14298) (concat (ashr (extract v_14291 64 96) v_14298) (ashr (extract v_14291 96 128) v_14298))));
      pure ()
    pat_end
