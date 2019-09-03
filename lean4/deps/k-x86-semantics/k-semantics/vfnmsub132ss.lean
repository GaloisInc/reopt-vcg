def vfnmsub132ss1 : instruction :=
  definst "vfnmsub132ss" $ do
    pattern fun (v_3331 : reg (bv 128)) (v_3332 : reg (bv 128)) (v_3333 : reg (bv 128)) => do
      v_7492 <- getRegister v_3333;
      v_7496 <- getRegister v_3331;
      v_7501 <- getRegister v_3332;
      setRegister (lhs.of_reg v_3333) (concat (extract v_7492 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7492 96 128) 24 8) (MInt2Float (extract v_7496 96 128) 24 8))) (MInt2Float (extract v_7501 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_3328 : Mem) (v_3326 : reg (bv 128)) (v_3327 : reg (bv 128)) => do
      v_13158 <- getRegister v_3327;
      v_13162 <- evaluateAddress v_3328;
      v_13163 <- load v_13162 4;
      v_13167 <- getRegister v_3326;
      setRegister (lhs.of_reg v_3327) (concat (extract v_13158 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13158 96 128) 24 8) (MInt2Float v_13163 24 8))) (MInt2Float (extract v_13167 96 128) 24 8)) 32));
      pure ()
    pat_end
