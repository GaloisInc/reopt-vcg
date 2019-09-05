def vfmadd213ps1 : instruction :=
  definst "vfmadd213ps" $ do
    pattern fun (v_2571 : reg (bv 128)) (v_2572 : reg (bv 128)) (v_2573 : reg (bv 128)) => do
      v_4396 <- getRegister v_2572;
      v_4399 <- getRegister v_2573;
      v_4403 <- getRegister v_2571;
      v_4405 <- eval (MInt2Float (extract v_4403 0 32) 24 8);
      v_4419 <- eval (MInt2Float (extract v_4403 32 64) 24 8);
      v_4434 <- eval (MInt2Float (extract v_4403 64 96) 24 8);
      v_4448 <- eval (MInt2Float (extract v_4403 96 128) 24 8);
      setRegister (lhs.of_reg v_2573) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4396 0 32) 24 8) (MInt2Float (extract v_4399 0 32) 24 8)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) v_4405)) v_4405) 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4396 32 64) 24 8) (MInt2Float (extract v_4399 32 64) 24 8)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) v_4419)) v_4419) 32) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4396 64 96) 24 8) (MInt2Float (extract v_4399 64 96) 24 8)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) v_4434)) v_4434) 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4396 96 128) 24 8) (MInt2Float (extract v_4399 96 128) 24 8)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) v_4448)) v_4448) 32) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2581 : reg (bv 256)) (v_2582 : reg (bv 256)) (v_2583 : reg (bv 256)) => do
      v_4464 <- getRegister v_2582;
      v_4467 <- getRegister v_2583;
      v_4471 <- getRegister v_2581;
      setRegister (lhs.of_reg v_2583) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4464 0 32) 24 8) (MInt2Float (extract v_4467 0 32) 24 8)) (MInt2Float (extract v_4471 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4464 32 64) 24 8) (MInt2Float (extract v_4467 32 64) 24 8)) (MInt2Float (extract v_4471 32 64) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4464 64 96) 24 8) (MInt2Float (extract v_4467 64 96) 24 8)) (MInt2Float (extract v_4471 64 96) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4464 96 128) 24 8) (MInt2Float (extract v_4467 96 128) 24 8)) (MInt2Float (extract v_4471 96 128) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4464 128 160) 24 8) (MInt2Float (extract v_4467 128 160) 24 8)) (MInt2Float (extract v_4471 128 160) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4464 160 192) 24 8) (MInt2Float (extract v_4467 160 192) 24 8)) (MInt2Float (extract v_4471 160 192) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4464 192 224) 24 8) (MInt2Float (extract v_4467 192 224) 24 8)) (MInt2Float (extract v_4471 192 224) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4464 224 256) 24 8) (MInt2Float (extract v_4467 224 256) 24 8)) (MInt2Float (extract v_4471 224 256) 24 8)) 32)))))));
      pure ()
    pat_end;
    pattern fun (v_2565 : Mem) (v_2566 : reg (bv 128)) (v_2567 : reg (bv 128)) => do
      v_10396 <- getRegister v_2566;
      v_10399 <- getRegister v_2567;
      v_10403 <- evaluateAddress v_2565;
      v_10404 <- load v_10403 16;
      v_10406 <- eval (MInt2Float (extract v_10404 0 32) 24 8);
      v_10420 <- eval (MInt2Float (extract v_10404 32 64) 24 8);
      v_10435 <- eval (MInt2Float (extract v_10404 64 96) 24 8);
      v_10449 <- eval (MInt2Float (extract v_10404 96 128) 24 8);
      setRegister (lhs.of_reg v_2567) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10396 0 32) 24 8) (MInt2Float (extract v_10399 0 32) 24 8)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) v_10406)) v_10406) 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10396 32 64) 24 8) (MInt2Float (extract v_10399 32 64) 24 8)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) v_10420)) v_10420) 32) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10396 64 96) 24 8) (MInt2Float (extract v_10399 64 96) 24 8)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) v_10435)) v_10435) 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10396 96 128) 24 8) (MInt2Float (extract v_10399 96 128) 24 8)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 32 0) 24 8) v_10449)) v_10449) 32) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2576 : Mem) (v_2577 : reg (bv 256)) (v_2578 : reg (bv 256)) => do
      v_10460 <- getRegister v_2577;
      v_10463 <- getRegister v_2578;
      v_10467 <- evaluateAddress v_2576;
      v_10468 <- load v_10467 32;
      setRegister (lhs.of_reg v_2578) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10460 0 32) 24 8) (MInt2Float (extract v_10463 0 32) 24 8)) (MInt2Float (extract v_10468 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10460 32 64) 24 8) (MInt2Float (extract v_10463 32 64) 24 8)) (MInt2Float (extract v_10468 32 64) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10460 64 96) 24 8) (MInt2Float (extract v_10463 64 96) 24 8)) (MInt2Float (extract v_10468 64 96) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10460 96 128) 24 8) (MInt2Float (extract v_10463 96 128) 24 8)) (MInt2Float (extract v_10468 96 128) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10460 128 160) 24 8) (MInt2Float (extract v_10463 128 160) 24 8)) (MInt2Float (extract v_10468 128 160) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10460 160 192) 24 8) (MInt2Float (extract v_10463 160 192) 24 8)) (MInt2Float (extract v_10468 160 192) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10460 192 224) 24 8) (MInt2Float (extract v_10463 192 224) 24 8)) (MInt2Float (extract v_10468 192 224) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10460 224 256) 24 8) (MInt2Float (extract v_10463 224 256) 24 8)) (MInt2Float (extract v_10468 224 256) 24 8)) 32)))))));
      pure ()
    pat_end
