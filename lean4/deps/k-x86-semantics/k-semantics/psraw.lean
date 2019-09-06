def psraw1 : instruction :=
  definst "psraw" $ do
    pattern fun (v_3107 : imm int) (v_3108 : reg (bv 128)) => do
      v_7766 <- getRegister v_3108;
      v_7768 <- eval (handleImmediateWithSignExtend v_3107 8 8);
      v_7772 <- eval (mux (ugt (concat (expression.bv_nat 56 0) v_7768) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (concat (expression.bv_nat 8 0) v_7768));
      setRegister (lhs.of_reg v_3108) (concat (ashr (extract v_7766 0 16) v_7772) (concat (ashr (extract v_7766 16 32) v_7772) (concat (ashr (extract v_7766 32 48) v_7772) (concat (ashr (extract v_7766 48 64) v_7772) (concat (ashr (extract v_7766 64 80) v_7772) (concat (ashr (extract v_7766 80 96) v_7772) (concat (ashr (extract v_7766 96 112) v_7772) (ashr (extract v_7766 112 128) v_7772))))))));
      pure ()
    pat_end;
    pattern fun (v_3116 : reg (bv 128)) (v_3117 : reg (bv 128)) => do
      v_7800 <- getRegister v_3117;
      v_7802 <- getRegister v_3116;
      v_7806 <- eval (mux (ugt (extract v_7802 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (extract v_7802 112 128));
      setRegister (lhs.of_reg v_3117) (concat (ashr (extract v_7800 0 16) v_7806) (concat (ashr (extract v_7800 16 32) v_7806) (concat (ashr (extract v_7800 32 48) v_7806) (concat (ashr (extract v_7800 48 64) v_7806) (concat (ashr (extract v_7800 64 80) v_7806) (concat (ashr (extract v_7800 80 96) v_7806) (concat (ashr (extract v_7800 96 112) v_7806) (ashr (extract v_7800 112 128) v_7806))))))));
      pure ()
    pat_end;
    pattern fun (v_3112 : Mem) (v_3113 : reg (bv 128)) => do
      v_14310 <- getRegister v_3113;
      v_14312 <- evaluateAddress v_3112;
      v_14313 <- load v_14312 16;
      v_14317 <- eval (mux (ugt (extract v_14313 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (extract v_14313 112 128));
      setRegister (lhs.of_reg v_3113) (concat (ashr (extract v_14310 0 16) v_14317) (concat (ashr (extract v_14310 16 32) v_14317) (concat (ashr (extract v_14310 32 48) v_14317) (concat (ashr (extract v_14310 48 64) v_14317) (concat (ashr (extract v_14310 64 80) v_14317) (concat (ashr (extract v_14310 80 96) v_14317) (concat (ashr (extract v_14310 96 112) v_14317) (ashr (extract v_14310 112 128) v_14317))))))));
      pure ()
    pat_end
