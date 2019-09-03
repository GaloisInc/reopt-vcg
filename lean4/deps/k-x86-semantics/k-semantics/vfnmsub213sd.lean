def vfnmsub213sd1 : instruction :=
  definst "vfnmsub213sd" $ do
    pattern fun (v_3386 : reg (bv 128)) (v_3387 : reg (bv 128)) (v_3388 : reg (bv 128)) => do
      v_7743 <- getRegister v_3388;
      v_7745 <- getRegister v_3387;
      v_7752 <- getRegister v_3386;
      setRegister (lhs.of_reg v_3388) (concat (extract v_7743 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7745 64 128) 53 11) (MInt2Float (extract v_7743 64 128) 53 11))) (MInt2Float (extract v_7752 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3383 : Mem) (v_3381 : reg (bv 128)) (v_3382 : reg (bv 128)) => do
      v_13388 <- getRegister v_3382;
      v_13390 <- getRegister v_3381;
      v_13397 <- evaluateAddress v_3383;
      v_13398 <- load v_13397 8;
      setRegister (lhs.of_reg v_3382) (concat (extract v_13388 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13390 64 128) 53 11) (MInt2Float (extract v_13388 64 128) 53 11))) (MInt2Float v_13398 53 11)) 64));
      pure ()
    pat_end
