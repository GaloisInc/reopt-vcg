def vfmadd213ps1 : instruction :=
  definst "vfmadd213ps" $ do
    pattern fun (v_2595 : reg (bv 128)) (v_2596 : reg (bv 128)) (v_2597 : reg (bv 128)) => do
      v_4423 <- getRegister v_2596;
      v_4426 <- getRegister v_2597;
      v_4430 <- getRegister v_2595;
      v_4432 <- eval (MInt2Float (extract v_4430 0 32) 24 8);
      v_4446 <- eval (MInt2Float (extract v_4430 32 64) 24 8);
      v_4461 <- eval (MInt2Float (extract v_4430 64 96) 24 8);
      v_4475 <- eval (MInt2Float (extract v_4430 96 128) 24 8);
      setRegister (lhs.of_reg v_2597) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4423 0 32) 24 8) (MInt2Float (extract v_4426 0 32) 24 8)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) v_4432)) v_4432) 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4423 32 64) 24 8) (MInt2Float (extract v_4426 32 64) 24 8)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) v_4446)) v_4446) 32) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4423 64 96) 24 8) (MInt2Float (extract v_4426 64 96) 24 8)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) v_4461)) v_4461) 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4423 96 128) 24 8) (MInt2Float (extract v_4426 96 128) 24 8)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) v_4475)) v_4475) 32) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2609 : reg (bv 256)) (v_2610 : reg (bv 256)) (v_2611 : reg (bv 256)) => do
      v_4491 <- getRegister v_2610;
      v_4494 <- getRegister v_2611;
      v_4498 <- getRegister v_2609;
      setRegister (lhs.of_reg v_2611) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4491 0 32) 24 8) (MInt2Float (extract v_4494 0 32) 24 8)) (MInt2Float (extract v_4498 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4491 32 64) 24 8) (MInt2Float (extract v_4494 32 64) 24 8)) (MInt2Float (extract v_4498 32 64) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4491 64 96) 24 8) (MInt2Float (extract v_4494 64 96) 24 8)) (MInt2Float (extract v_4498 64 96) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4491 96 128) 24 8) (MInt2Float (extract v_4494 96 128) 24 8)) (MInt2Float (extract v_4498 96 128) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4491 128 160) 24 8) (MInt2Float (extract v_4494 128 160) 24 8)) (MInt2Float (extract v_4498 128 160) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4491 160 192) 24 8) (MInt2Float (extract v_4494 160 192) 24 8)) (MInt2Float (extract v_4498 160 192) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4491 192 224) 24 8) (MInt2Float (extract v_4494 192 224) 24 8)) (MInt2Float (extract v_4498 192 224) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4491 224 256) 24 8) (MInt2Float (extract v_4494 224 256) 24 8)) (MInt2Float (extract v_4498 224 256) 24 8)) 32)))))));
      pure ()
    pat_end;
    pattern fun (v_2592 : Mem) (v_2590 : reg (bv 128)) (v_2591 : reg (bv 128)) => do
      v_10423 <- getRegister v_2590;
      v_10426 <- getRegister v_2591;
      v_10430 <- evaluateAddress v_2592;
      v_10431 <- load v_10430 16;
      v_10433 <- eval (MInt2Float (extract v_10431 0 32) 24 8);
      v_10447 <- eval (MInt2Float (extract v_10431 32 64) 24 8);
      v_10462 <- eval (MInt2Float (extract v_10431 64 96) 24 8);
      v_10476 <- eval (MInt2Float (extract v_10431 96 128) 24 8);
      setRegister (lhs.of_reg v_2591) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10423 0 32) 24 8) (MInt2Float (extract v_10426 0 32) 24 8)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) v_10433)) v_10433) 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10423 32 64) 24 8) (MInt2Float (extract v_10426 32 64) 24 8)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) v_10447)) v_10447) 32) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10423 64 96) 24 8) (MInt2Float (extract v_10426 64 96) 24 8)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) v_10462)) v_10462) 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10423 96 128) 24 8) (MInt2Float (extract v_10426 96 128) 24 8)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) v_10476)) v_10476) 32) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2601 : Mem) (v_2604 : reg (bv 256)) (v_2605 : reg (bv 256)) => do
      v_10487 <- getRegister v_2604;
      v_10490 <- getRegister v_2605;
      v_10494 <- evaluateAddress v_2601;
      v_10495 <- load v_10494 32;
      setRegister (lhs.of_reg v_2605) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10487 0 32) 24 8) (MInt2Float (extract v_10490 0 32) 24 8)) (MInt2Float (extract v_10495 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10487 32 64) 24 8) (MInt2Float (extract v_10490 32 64) 24 8)) (MInt2Float (extract v_10495 32 64) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10487 64 96) 24 8) (MInt2Float (extract v_10490 64 96) 24 8)) (MInt2Float (extract v_10495 64 96) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10487 96 128) 24 8) (MInt2Float (extract v_10490 96 128) 24 8)) (MInt2Float (extract v_10495 96 128) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10487 128 160) 24 8) (MInt2Float (extract v_10490 128 160) 24 8)) (MInt2Float (extract v_10495 128 160) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10487 160 192) 24 8) (MInt2Float (extract v_10490 160 192) 24 8)) (MInt2Float (extract v_10495 160 192) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10487 192 224) 24 8) (MInt2Float (extract v_10490 192 224) 24 8)) (MInt2Float (extract v_10495 192 224) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10487 224 256) 24 8) (MInt2Float (extract v_10490 224 256) 24 8)) (MInt2Float (extract v_10495 224 256) 24 8)) 32)))))));
      pure ()
    pat_end
