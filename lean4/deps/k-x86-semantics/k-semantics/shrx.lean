def shrx1 : instruction :=
  definst "shrx" $ do
    pattern fun (v_3062 : reg (bv 32)) (v_3063 : reg (bv 32)) (v_3064 : reg (bv 32)) => do
      v_7215 <- getRegister v_3063;
      v_7216 <- getRegister v_3062;
      setRegister (lhs.of_reg v_3064) (lshr v_7215 (bv_and v_7216 (expression.bv_nat 32 31)));
      pure ()
    pat_end;
    pattern fun (v_3083 : reg (bv 64)) (v_3084 : reg (bv 64)) (v_3085 : reg (bv 64)) => do
      v_7231 <- getRegister v_3084;
      v_7233 <- getRegister v_3083;
      setRegister (lhs.of_reg v_3085) (extract (lshr (concat v_7231 (expression.bv_nat 1 0)) (concat (expression.bv_nat 57 0) (bv_and (extract v_7233 56 64) (expression.bv_nat 8 63)))) 0 64);
      pure ()
    pat_end;
    pattern fun (v_3053 : reg (bv 32)) (v_3052 : Mem) (v_3054 : reg (bv 32)) => do
      v_10762 <- evaluateAddress v_3052;
      v_10763 <- load v_10762 4;
      v_10764 <- getRegister v_3053;
      setRegister (lhs.of_reg v_3054) (lshr v_10763 (bv_and v_10764 (expression.bv_nat 32 31)));
      pure ()
    pat_end;
    pattern fun (v_3074 : reg (bv 64)) (v_3073 : Mem) (v_3075 : reg (bv 64)) => do
      v_10768 <- evaluateAddress v_3073;
      v_10769 <- load v_10768 8;
      v_10771 <- getRegister v_3074;
      setRegister (lhs.of_reg v_3075) (extract (lshr (concat v_10769 (expression.bv_nat 1 0)) (concat (expression.bv_nat 57 0) (bv_and (extract v_10771 56 64) (expression.bv_nat 8 63)))) 0 64);
      pure ()
    pat_end
