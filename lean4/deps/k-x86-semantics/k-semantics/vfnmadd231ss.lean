def vfnmadd231ss1 : instruction :=
  definst "vfnmadd231ss" $ do
    pattern fun (v_3330 : reg (bv 128)) (v_3331 : reg (bv 128)) (v_3332 : reg (bv 128)) => do
      v_7292 <- getRegister v_3332;
      v_7294 <- getRegister v_3331;
      v_7297 <- getRegister v_3330;
      v_7303 <- eval (MInt2Float (extract v_7292 96 128) 24 8);
      setRegister (lhs.of_reg v_3332) (concat (extract v_7292 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7294 96 128) 24 8) (MInt2Float (extract v_7297 96 128) 24 8))) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) v_7303)) v_7303) 32) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_3324 : Mem) (v_3325 : reg (bv 128)) (v_3326 : reg (bv 128)) => do
      v_13001 <- getRegister v_3326;
      v_13003 <- getRegister v_3325;
      v_13006 <- evaluateAddress v_3324;
      v_13007 <- load v_13006 4;
      v_13012 <- eval (MInt2Float (extract v_13001 96 128) 24 8);
      setRegister (lhs.of_reg v_3326) (concat (extract v_13001 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13003 96 128) 24 8) (MInt2Float v_13007 24 8))) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) v_13012)) v_13012) 32) 24 8)) 32));
      pure ()
    pat_end
