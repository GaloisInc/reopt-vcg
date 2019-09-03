def shrx1 : instruction :=
  definst "shrx" $ do
    pattern fun (v_3011 : reg (bv 32)) (v_3012 : reg (bv 32)) (v_3013 : reg (bv 32)) => do
      v_8190 <- getRegister v_3012;
      v_8191 <- getRegister v_3011;
      setRegister (lhs.of_reg v_3013) (lshr v_8190 (uvalueMInt (bv_and v_8191 (expression.bv_nat 32 31))));
      pure ()
    pat_end;
    pattern fun (v_3032 : reg (bv 64)) (v_3033 : reg (bv 64)) (v_3034 : reg (bv 64)) => do
      v_8207 <- getRegister v_3033;
      v_8209 <- getRegister v_3032;
      setRegister (lhs.of_reg v_3034) (extract (lshr (concat v_8207 (expression.bv_nat 1 0)) (uvalueMInt (concat (expression.bv_nat 57 0) (bv_and (extract v_8209 56 64) (expression.bv_nat 8 63))))) 0 64);
      pure ()
    pat_end;
    pattern fun (v_3001 : reg (bv 32)) (v_3003 : Mem) (v_3002 : reg (bv 32)) => do
      v_13003 <- evaluateAddress v_3003;
      v_13004 <- load v_13003 4;
      v_13005 <- getRegister v_3001;
      setRegister (lhs.of_reg v_3002) (lshr v_13004 (uvalueMInt (bv_and v_13005 (expression.bv_nat 32 31))));
      pure ()
    pat_end;
    pattern fun (v_3022 : reg (bv 64)) (v_3024 : Mem) (v_3023 : reg (bv 64)) => do
      v_13010 <- evaluateAddress v_3024;
      v_13011 <- load v_13010 8;
      v_13013 <- getRegister v_3022;
      setRegister (lhs.of_reg v_3023) (extract (lshr (concat v_13011 (expression.bv_nat 1 0)) (uvalueMInt (concat (expression.bv_nat 57 0) (bv_and (extract v_13013 56 64) (expression.bv_nat 8 63))))) 0 64);
      pure ()
    pat_end
