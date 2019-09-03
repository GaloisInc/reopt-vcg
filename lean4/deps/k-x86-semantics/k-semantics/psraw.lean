def psraw1 : instruction :=
  definst "psraw" $ do
    pattern fun (v_3030 : imm int) (v_3031 : reg (bv 128)) => do
      v_7762 <- getRegister v_3031;
      v_7766 <- eval (handleImmediateWithSignExtend v_3030 8 8);
      v_7771 <- eval (uvalueMInt (mux (ugt (concat (expression.bv_nat 56 0) v_7766) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (concat (expression.bv_nat 8 0) v_7766)));
      setRegister (lhs.of_reg v_3031) (concat (ashr (mi 16 (svalueMInt (extract v_7762 0 16))) v_7771) (concat (ashr (mi 16 (svalueMInt (extract v_7762 16 32))) v_7771) (concat (ashr (mi 16 (svalueMInt (extract v_7762 32 48))) v_7771) (concat (ashr (mi 16 (svalueMInt (extract v_7762 48 64))) v_7771) (concat (ashr (mi 16 (svalueMInt (extract v_7762 64 80))) v_7771) (concat (ashr (mi 16 (svalueMInt (extract v_7762 80 96))) v_7771) (concat (ashr (mi 16 (svalueMInt (extract v_7762 96 112))) v_7771) (ashr (mi 16 (svalueMInt (extract v_7762 112 128))) v_7771))))))));
      pure ()
    pat_end;
    pattern fun (v_3039 : reg (bv 128)) (v_3040 : reg (bv 128)) => do
      v_7813 <- getRegister v_3040;
      v_7817 <- getRegister v_3039;
      v_7822 <- eval (uvalueMInt (mux (ugt (extract v_7817 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (extract v_7817 112 128)));
      setRegister (lhs.of_reg v_3040) (concat (ashr (mi 16 (svalueMInt (extract v_7813 0 16))) v_7822) (concat (ashr (mi 16 (svalueMInt (extract v_7813 16 32))) v_7822) (concat (ashr (mi 16 (svalueMInt (extract v_7813 32 48))) v_7822) (concat (ashr (mi 16 (svalueMInt (extract v_7813 48 64))) v_7822) (concat (ashr (mi 16 (svalueMInt (extract v_7813 64 80))) v_7822) (concat (ashr (mi 16 (svalueMInt (extract v_7813 80 96))) v_7822) (concat (ashr (mi 16 (svalueMInt (extract v_7813 96 112))) v_7822) (ashr (mi 16 (svalueMInt (extract v_7813 112 128))) v_7822))))))));
      pure ()
    pat_end;
    pattern fun (v_3035 : Mem) (v_3036 : reg (bv 128)) => do
      v_14516 <- getRegister v_3036;
      v_14520 <- evaluateAddress v_3035;
      v_14521 <- load v_14520 16;
      v_14526 <- eval (uvalueMInt (mux (ugt (extract v_14521 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (extract v_14521 112 128)));
      setRegister (lhs.of_reg v_3036) (concat (ashr (mi 16 (svalueMInt (extract v_14516 0 16))) v_14526) (concat (ashr (mi 16 (svalueMInt (extract v_14516 16 32))) v_14526) (concat (ashr (mi 16 (svalueMInt (extract v_14516 32 48))) v_14526) (concat (ashr (mi 16 (svalueMInt (extract v_14516 48 64))) v_14526) (concat (ashr (mi 16 (svalueMInt (extract v_14516 64 80))) v_14526) (concat (ashr (mi 16 (svalueMInt (extract v_14516 80 96))) v_14526) (concat (ashr (mi 16 (svalueMInt (extract v_14516 96 112))) v_14526) (ashr (mi 16 (svalueMInt (extract v_14516 112 128))) v_14526))))))));
      pure ()
    pat_end
