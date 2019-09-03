def vfmadd213ps1 : instruction :=
  definst "vfmadd213ps" $ do
    pattern fun (v_2506 : reg (bv 128)) (v_2507 : reg (bv 128)) (v_2508 : reg (bv 128)) => do
      v_4336 <- getRegister v_2507;
      v_4339 <- getRegister v_2508;
      v_4343 <- getRegister v_2506;
      v_4345 <- eval (MInt2Float (extract v_4343 0 32) 24 8);
      v_4359 <- eval (MInt2Float (extract v_4343 32 64) 24 8);
      v_4374 <- eval (MInt2Float (extract v_4343 64 96) 24 8);
      v_4388 <- eval (MInt2Float (extract v_4343 96 128) 24 8);
      setRegister (lhs.of_reg v_2508) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4336 0 32) 24 8) (MInt2Float (extract v_4339 0 32) 24 8)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT 0e+00 v_4345)) v_4345) 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4336 32 64) 24 8) (MInt2Float (extract v_4339 32 64) 24 8)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT 0e+00 v_4359)) v_4359) 32) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4336 64 96) 24 8) (MInt2Float (extract v_4339 64 96) 24 8)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT 0e+00 v_4374)) v_4374) 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4336 96 128) 24 8) (MInt2Float (extract v_4339 96 128) 24 8)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT 0e+00 v_4388)) v_4388) 32) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2518 : reg (bv 256)) (v_2519 : reg (bv 256)) (v_2520 : reg (bv 256)) => do
      v_4404 <- getRegister v_2519;
      v_4407 <- getRegister v_2520;
      v_4411 <- getRegister v_2518;
      setRegister (lhs.of_reg v_2520) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4404 0 32) 24 8) (MInt2Float (extract v_4407 0 32) 24 8)) (MInt2Float (extract v_4411 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4404 32 64) 24 8) (MInt2Float (extract v_4407 32 64) 24 8)) (MInt2Float (extract v_4411 32 64) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4404 64 96) 24 8) (MInt2Float (extract v_4407 64 96) 24 8)) (MInt2Float (extract v_4411 64 96) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4404 96 128) 24 8) (MInt2Float (extract v_4407 96 128) 24 8)) (MInt2Float (extract v_4411 96 128) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4404 128 160) 24 8) (MInt2Float (extract v_4407 128 160) 24 8)) (MInt2Float (extract v_4411 128 160) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4404 160 192) 24 8) (MInt2Float (extract v_4407 160 192) 24 8)) (MInt2Float (extract v_4411 160 192) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4404 192 224) 24 8) (MInt2Float (extract v_4407 192 224) 24 8)) (MInt2Float (extract v_4411 192 224) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4404 224 256) 24 8) (MInt2Float (extract v_4407 224 256) 24 8)) (MInt2Float (extract v_4411 224 256) 24 8)) 32)))))));
      pure ()
    pat_end;
    pattern fun (v_2503 : Mem) (v_2501 : reg (bv 128)) (v_2502 : reg (bv 128)) => do
      v_10319 <- getRegister v_2501;
      v_10322 <- getRegister v_2502;
      v_10326 <- evaluateAddress v_2503;
      v_10327 <- load v_10326 16;
      v_10329 <- eval (MInt2Float (extract v_10327 0 32) 24 8);
      v_10343 <- eval (MInt2Float (extract v_10327 32 64) 24 8);
      v_10358 <- eval (MInt2Float (extract v_10327 64 96) 24 8);
      v_10372 <- eval (MInt2Float (extract v_10327 96 128) 24 8);
      setRegister (lhs.of_reg v_2502) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10319 0 32) 24 8) (MInt2Float (extract v_10322 0 32) 24 8)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT 0e+00 v_10329)) v_10329) 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10319 32 64) 24 8) (MInt2Float (extract v_10322 32 64) 24 8)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT 0e+00 v_10343)) v_10343) 32) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10319 64 96) 24 8) (MInt2Float (extract v_10322 64 96) 24 8)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT 0e+00 v_10358)) v_10358) 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10319 96 128) 24 8) (MInt2Float (extract v_10322 96 128) 24 8)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT 0e+00 v_10372)) v_10372) 32) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2512 : Mem) (v_2513 : reg (bv 256)) (v_2514 : reg (bv 256)) => do
      v_10383 <- getRegister v_2513;
      v_10386 <- getRegister v_2514;
      v_10390 <- evaluateAddress v_2512;
      v_10391 <- load v_10390 32;
      setRegister (lhs.of_reg v_2514) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10383 0 32) 24 8) (MInt2Float (extract v_10386 0 32) 24 8)) (MInt2Float (extract v_10391 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10383 32 64) 24 8) (MInt2Float (extract v_10386 32 64) 24 8)) (MInt2Float (extract v_10391 32 64) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10383 64 96) 24 8) (MInt2Float (extract v_10386 64 96) 24 8)) (MInt2Float (extract v_10391 64 96) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10383 96 128) 24 8) (MInt2Float (extract v_10386 96 128) 24 8)) (MInt2Float (extract v_10391 96 128) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10383 128 160) 24 8) (MInt2Float (extract v_10386 128 160) 24 8)) (MInt2Float (extract v_10391 128 160) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10383 160 192) 24 8) (MInt2Float (extract v_10386 160 192) 24 8)) (MInt2Float (extract v_10391 160 192) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10383 192 224) 24 8) (MInt2Float (extract v_10386 192 224) 24 8)) (MInt2Float (extract v_10391 192 224) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10383 224 256) 24 8) (MInt2Float (extract v_10386 224 256) 24 8)) (MInt2Float (extract v_10391 224 256) 24 8)) 32)))))));
      pure ()
    pat_end
