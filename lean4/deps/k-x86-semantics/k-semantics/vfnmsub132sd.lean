def vfnmsub132sd1 : instruction :=
  definst "vfnmsub132sd" $ do
    pattern fun (v_3385 : reg (bv 128)) (v_3386 : reg (bv 128)) (v_3387 : reg (bv 128)) => do
      v_7548 <- getRegister v_3387;
      v_7552 <- getRegister v_3385;
      v_7557 <- getRegister v_3386;
      setRegister (lhs.of_reg v_3387) (concat (extract v_7548 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7548 64 128) 53 11) (MInt2Float (extract v_7552 64 128) 53 11))) (MInt2Float (extract v_7557 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3379 : Mem) (v_3380 : reg (bv 128)) (v_3381 : reg (bv 128)) => do
      v_13236 <- getRegister v_3381;
      v_13240 <- evaluateAddress v_3379;
      v_13241 <- load v_13240 8;
      v_13245 <- getRegister v_3380;
      setRegister (lhs.of_reg v_3381) (concat (extract v_13236 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13236 64 128) 53 11) (MInt2Float v_13241 53 11))) (MInt2Float (extract v_13245 64 128) 53 11)) 64));
      pure ()
    pat_end
