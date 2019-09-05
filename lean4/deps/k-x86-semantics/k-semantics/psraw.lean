def psraw1 : instruction :=
  definst "psraw" $ do
    pattern fun (v_3080 : imm int) (v_3079 : reg (bv 128)) => do
      v_7739 <- getRegister v_3079;
      v_7741 <- eval (handleImmediateWithSignExtend v_3080 8 8);
      v_7745 <- eval (mux (ugt (concat (expression.bv_nat 56 0) v_7741) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (concat (expression.bv_nat 8 0) v_7741));
      setRegister (lhs.of_reg v_3079) (concat (ashr (extract v_7739 0 16) v_7745) (concat (ashr (extract v_7739 16 32) v_7745) (concat (ashr (extract v_7739 32 48) v_7745) (concat (ashr (extract v_7739 48 64) v_7745) (concat (ashr (extract v_7739 64 80) v_7745) (concat (ashr (extract v_7739 80 96) v_7745) (concat (ashr (extract v_7739 96 112) v_7745) (ashr (extract v_7739 112 128) v_7745))))))));
      pure ()
    pat_end;
    pattern fun (v_3088 : reg (bv 128)) (v_3089 : reg (bv 128)) => do
      v_7773 <- getRegister v_3089;
      v_7775 <- getRegister v_3088;
      v_7779 <- eval (mux (ugt (extract v_7775 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (extract v_7775 112 128));
      setRegister (lhs.of_reg v_3089) (concat (ashr (extract v_7773 0 16) v_7779) (concat (ashr (extract v_7773 16 32) v_7779) (concat (ashr (extract v_7773 32 48) v_7779) (concat (ashr (extract v_7773 48 64) v_7779) (concat (ashr (extract v_7773 64 80) v_7779) (concat (ashr (extract v_7773 80 96) v_7779) (concat (ashr (extract v_7773 96 112) v_7779) (ashr (extract v_7773 112 128) v_7779))))))));
      pure ()
    pat_end;
    pattern fun (v_3085 : Mem) (v_3084 : reg (bv 128)) => do
      v_14334 <- getRegister v_3084;
      v_14336 <- evaluateAddress v_3085;
      v_14337 <- load v_14336 16;
      v_14341 <- eval (mux (ugt (extract v_14337 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (extract v_14337 112 128));
      setRegister (lhs.of_reg v_3084) (concat (ashr (extract v_14334 0 16) v_14341) (concat (ashr (extract v_14334 16 32) v_14341) (concat (ashr (extract v_14334 32 48) v_14341) (concat (ashr (extract v_14334 48 64) v_14341) (concat (ashr (extract v_14334 64 80) v_14341) (concat (ashr (extract v_14334 80 96) v_14341) (concat (ashr (extract v_14334 96 112) v_14341) (ashr (extract v_14334 112 128) v_14341))))))));
      pure ()
    pat_end
