def shrxq1 : instruction :=
  definst "shrxq" $ do
    pattern fun (v_3037 : reg (bv 64)) (v_3038 : reg (bv 64)) (v_3039 : reg (bv 64)) => do
      v_6642 <- getRegister v_3038;
      v_6644 <- getRegister v_3037;
      setRegister (lhs.of_reg v_3039) (extract (lshr (concat v_6642 (expression.bv_nat 1 0)) (uvalueMInt (concat (expression.bv_nat 57 0) (bv_and (extract v_6644 56 64) (expression.bv_nat 8 63))))) 0 64);
      pure ()
    pat_end;
    pattern fun (v_3028 : reg (bv 64)) (v_3027 : Mem) (v_3029 : reg (bv 64)) => do
      v_10200 <- evaluateAddress v_3027;
      v_10201 <- load v_10200 8;
      v_10203 <- getRegister v_3028;
      setRegister (lhs.of_reg v_3029) (extract (lshr (concat v_10201 (expression.bv_nat 1 0)) (uvalueMInt (concat (expression.bv_nat 57 0) (bv_and (extract v_10203 56 64) (expression.bv_nat 8 63))))) 0 64);
      pure ()
    pat_end
