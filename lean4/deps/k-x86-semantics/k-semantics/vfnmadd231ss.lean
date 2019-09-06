def vfnmadd231ss1 : instruction :=
  definst "vfnmadd231ss" $ do
    pattern fun (v_3354 : reg (bv 128)) (v_3355 : reg (bv 128)) (v_3356 : reg (bv 128)) => do
      v_7319 <- getRegister v_3356;
      v_7321 <- getRegister v_3355;
      v_7324 <- getRegister v_3354;
      v_7330 <- eval (MInt2Float (extract v_7319 96 128) 24 8);
      setRegister (lhs.of_reg v_3356) (concat (extract v_7319 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7321 96 128) 24 8) (MInt2Float (extract v_7324 96 128) 24 8))) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) v_7330)) v_7330) 32) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_3351 : Mem) (v_3349 : reg (bv 128)) (v_3350 : reg (bv 128)) => do
      v_13028 <- getRegister v_3350;
      v_13030 <- getRegister v_3349;
      v_13033 <- evaluateAddress v_3351;
      v_13034 <- load v_13033 4;
      v_13039 <- eval (MInt2Float (extract v_13028 96 128) 24 8);
      setRegister (lhs.of_reg v_3350) (concat (extract v_13028 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13030 96 128) 24 8) (MInt2Float v_13034 24 8))) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) v_13039)) v_13039) 32) 24 8)) 32));
      pure ()
    pat_end
