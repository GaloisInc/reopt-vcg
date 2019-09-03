def shrxq1 : instruction :=
  definst "shrxq" $ do
    pattern fun (v_3025 : reg (bv 64)) (v_3026 : reg (bv 64)) (v_3027 : reg (bv 64)) => do
      v_6646 <- getRegister v_3026;
      v_6648 <- getRegister v_3025;
      setRegister (lhs.of_reg v_3027) (extract (lshr (concat v_6646 (expression.bv_nat 1 0)) (uvalueMInt (concat (expression.bv_nat 57 0) (bv_and (extract v_6648 56 64) (expression.bv_nat 8 63))))) 0 64);
      pure ()
    pat_end;
    pattern fun (v_3015 : reg (bv 64)) (v_3014 : Mem) (v_3016 : reg (bv 64)) => do
      v_10178 <- evaluateAddress v_3014;
      v_10179 <- load v_10178 8;
      v_10181 <- getRegister v_3015;
      setRegister (lhs.of_reg v_3016) (extract (lshr (concat v_10179 (expression.bv_nat 1 0)) (uvalueMInt (concat (expression.bv_nat 57 0) (bv_and (extract v_10181 56 64) (expression.bv_nat 8 63))))) 0 64);
      pure ()
    pat_end
