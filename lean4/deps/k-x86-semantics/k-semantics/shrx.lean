def shrx1 : instruction :=
  definst "shrx" $ do
    pattern fun (v_2998 : reg (bv 32)) (v_2999 : reg (bv 32)) (v_3000 : reg (bv 32)) => do
      v_8166 <- getRegister v_2999;
      v_8167 <- getRegister v_2998;
      setRegister (lhs.of_reg v_3000) (lshr v_8166 (uvalueMInt (bv_and v_8167 (expression.bv_nat 32 31))));
      pure ()
    pat_end;
    pattern fun (v_3019 : reg (bv 64)) (v_3020 : reg (bv 64)) (v_3021 : reg (bv 64)) => do
      v_8183 <- getRegister v_3020;
      v_8185 <- getRegister v_3019;
      setRegister (lhs.of_reg v_3021) (extract (lshr (concat v_8183 (expression.bv_nat 1 0)) (uvalueMInt (concat (expression.bv_nat 57 0) (bv_and (extract v_8185 56 64) (expression.bv_nat 8 63))))) 0 64);
      pure ()
    pat_end;
    pattern fun (v_2989 : reg (bv 32)) (v_2988 : Mem) (v_2990 : reg (bv 32)) => do
      v_12931 <- evaluateAddress v_2988;
      v_12932 <- load v_12931 4;
      v_12933 <- getRegister v_2989;
      setRegister (lhs.of_reg v_2990) (lshr v_12932 (uvalueMInt (bv_and v_12933 (expression.bv_nat 32 31))));
      pure ()
    pat_end;
    pattern fun (v_3010 : reg (bv 64)) (v_3009 : Mem) (v_3011 : reg (bv 64)) => do
      v_12938 <- evaluateAddress v_3009;
      v_12939 <- load v_12938 8;
      v_12941 <- getRegister v_3010;
      setRegister (lhs.of_reg v_3011) (extract (lshr (concat v_12939 (expression.bv_nat 1 0)) (uvalueMInt (concat (expression.bv_nat 57 0) (bv_and (extract v_12941 56 64) (expression.bv_nat 8 63))))) 0 64);
      pure ()
    pat_end
