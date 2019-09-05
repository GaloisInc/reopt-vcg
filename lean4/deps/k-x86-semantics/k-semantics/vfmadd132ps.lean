def vfmadd132ps1 : instruction :=
  definst "vfmadd132ps" $ do
    pattern fun (v_2505 : reg (bv 128)) (v_2506 : reg (bv 128)) (v_2507 : reg (bv 128)) => do
      v_4163 <- getRegister v_2507;
      v_4166 <- getRegister v_2505;
      v_4170 <- getRegister v_2506;
      setRegister (lhs.of_reg v_2507) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4163 0 32) 24 8) (MInt2Float (extract v_4166 0 32) 24 8)) (MInt2Float (extract v_4170 0 32) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4163 32 64) 24 8) (MInt2Float (extract v_4166 32 64) 24 8)) (MInt2Float (extract v_4170 32 64) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4163 64 96) 24 8) (MInt2Float (extract v_4166 64 96) 24 8)) (MInt2Float (extract v_4170 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4163 96 128) 24 8) (MInt2Float (extract v_4166 96 128) 24 8)) (MInt2Float (extract v_4170 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2515 : reg (bv 256)) (v_2516 : reg (bv 256)) (v_2517 : reg (bv 256)) => do
      v_4211 <- getRegister v_2517;
      v_4214 <- getRegister v_2515;
      v_4218 <- getRegister v_2516;
      setRegister (lhs.of_reg v_2517) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4211 0 32) 24 8) (MInt2Float (extract v_4214 0 32) 24 8)) (MInt2Float (extract v_4218 0 32) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4211 32 64) 24 8) (MInt2Float (extract v_4214 32 64) 24 8)) (MInt2Float (extract v_4218 32 64) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4211 64 96) 24 8) (MInt2Float (extract v_4214 64 96) 24 8)) (MInt2Float (extract v_4218 64 96) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4211 96 128) 24 8) (MInt2Float (extract v_4214 96 128) 24 8)) (MInt2Float (extract v_4218 96 128) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4211 128 160) 24 8) (MInt2Float (extract v_4214 128 160) 24 8)) (MInt2Float (extract v_4218 128 160) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4211 160 192) 24 8) (MInt2Float (extract v_4214 160 192) 24 8)) (MInt2Float (extract v_4218 160 192) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4211 192 224) 24 8) (MInt2Float (extract v_4214 192 224) 24 8)) (MInt2Float (extract v_4218 192 224) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4211 224 256) 24 8) (MInt2Float (extract v_4214 224 256) 24 8)) (MInt2Float (extract v_4218 224 256) 24 8)) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_2499 : Mem) (v_2500 : reg (bv 128)) (v_2501 : reg (bv 128)) => do
      v_10189 <- getRegister v_2501;
      v_10192 <- evaluateAddress v_2499;
      v_10193 <- load v_10192 16;
      v_10197 <- getRegister v_2500;
      setRegister (lhs.of_reg v_2501) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10189 0 32) 24 8) (MInt2Float (extract v_10193 0 32) 24 8)) (MInt2Float (extract v_10197 0 32) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10189 32 64) 24 8) (MInt2Float (extract v_10193 32 64) 24 8)) (MInt2Float (extract v_10197 32 64) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10189 64 96) 24 8) (MInt2Float (extract v_10193 64 96) 24 8)) (MInt2Float (extract v_10197 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10189 96 128) 24 8) (MInt2Float (extract v_10193 96 128) 24 8)) (MInt2Float (extract v_10197 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2510 : Mem) (v_2511 : reg (bv 256)) (v_2512 : reg (bv 256)) => do
      v_10233 <- getRegister v_2512;
      v_10236 <- evaluateAddress v_2510;
      v_10237 <- load v_10236 32;
      v_10241 <- getRegister v_2511;
      setRegister (lhs.of_reg v_2512) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10233 0 32) 24 8) (MInt2Float (extract v_10237 0 32) 24 8)) (MInt2Float (extract v_10241 0 32) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10233 32 64) 24 8) (MInt2Float (extract v_10237 32 64) 24 8)) (MInt2Float (extract v_10241 32 64) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10233 64 96) 24 8) (MInt2Float (extract v_10237 64 96) 24 8)) (MInt2Float (extract v_10241 64 96) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10233 96 128) 24 8) (MInt2Float (extract v_10237 96 128) 24 8)) (MInt2Float (extract v_10241 96 128) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10233 128 160) 24 8) (MInt2Float (extract v_10237 128 160) 24 8)) (MInt2Float (extract v_10241 128 160) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10233 160 192) 24 8) (MInt2Float (extract v_10237 160 192) 24 8)) (MInt2Float (extract v_10241 160 192) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10233 192 224) 24 8) (MInt2Float (extract v_10237 192 224) 24 8)) (MInt2Float (extract v_10241 192 224) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10233 224 256) 24 8) (MInt2Float (extract v_10237 224 256) 24 8)) (MInt2Float (extract v_10241 224 256) 24 8)) 32))))))));
      pure ()
    pat_end
