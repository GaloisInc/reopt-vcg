def vfmadd231ps1 : instruction :=
  definst "vfmadd231ps" $ do
    pattern fun (v_2572 : reg (bv 128)) (v_2573 : reg (bv 128)) (v_2574 : reg (bv 128)) => do
      v_4594 <- getRegister v_2573;
      v_4597 <- getRegister v_2572;
      v_4601 <- getRegister v_2574;
      setRegister (lhs.of_reg v_2574) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4594 0 32) 24 8) (MInt2Float (extract v_4597 0 32) 24 8)) (MInt2Float (extract v_4601 0 32) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4594 32 64) 24 8) (MInt2Float (extract v_4597 32 64) 24 8)) (MInt2Float (extract v_4601 32 64) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4594 64 96) 24 8) (MInt2Float (extract v_4597 64 96) 24 8)) (MInt2Float (extract v_4601 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4594 96 128) 24 8) (MInt2Float (extract v_4597 96 128) 24 8)) (MInt2Float (extract v_4601 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2584 : reg (bv 256)) (v_2585 : reg (bv 256)) (v_2586 : reg (bv 256)) => do
      v_4642 <- getRegister v_2585;
      v_4645 <- getRegister v_2584;
      v_4649 <- getRegister v_2586;
      setRegister (lhs.of_reg v_2586) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4642 0 32) 24 8) (MInt2Float (extract v_4645 0 32) 24 8)) (MInt2Float (extract v_4649 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4642 32 64) 24 8) (MInt2Float (extract v_4645 32 64) 24 8)) (MInt2Float (extract v_4649 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4642 64 96) 24 8) (MInt2Float (extract v_4645 64 96) 24 8)) (MInt2Float (extract v_4649 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4642 96 128) 24 8) (MInt2Float (extract v_4645 96 128) 24 8)) (MInt2Float (extract v_4649 96 128) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4642 128 160) 24 8) (MInt2Float (extract v_4645 128 160) 24 8)) (MInt2Float (extract v_4649 128 160) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4642 160 192) 24 8) (MInt2Float (extract v_4645 160 192) 24 8)) (MInt2Float (extract v_4649 160 192) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4642 192 224) 24 8) (MInt2Float (extract v_4645 192 224) 24 8)) (MInt2Float (extract v_4649 192 224) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4642 224 256) 24 8) (MInt2Float (extract v_4645 224 256) 24 8)) (MInt2Float (extract v_4649 224 256) 24 8)) 32))))));
      pure ()
    pat_end;
    pattern fun (v_2569 : Mem) (v_2567 : reg (bv 128)) (v_2568 : reg (bv 128)) => do
      v_10551 <- getRegister v_2567;
      v_10554 <- evaluateAddress v_2569;
      v_10555 <- load v_10554 16;
      v_10559 <- getRegister v_2568;
      setRegister (lhs.of_reg v_2568) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10551 0 32) 24 8) (MInt2Float (extract v_10555 0 32) 24 8)) (MInt2Float (extract v_10559 0 32) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10551 32 64) 24 8) (MInt2Float (extract v_10555 32 64) 24 8)) (MInt2Float (extract v_10559 32 64) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10551 64 96) 24 8) (MInt2Float (extract v_10555 64 96) 24 8)) (MInt2Float (extract v_10559 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10551 96 128) 24 8) (MInt2Float (extract v_10555 96 128) 24 8)) (MInt2Float (extract v_10559 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2578 : Mem) (v_2579 : reg (bv 256)) (v_2580 : reg (bv 256)) => do
      v_10595 <- getRegister v_2579;
      v_10598 <- evaluateAddress v_2578;
      v_10599 <- load v_10598 32;
      v_10603 <- getRegister v_2580;
      setRegister (lhs.of_reg v_2580) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10595 0 32) 24 8) (MInt2Float (extract v_10599 0 32) 24 8)) (MInt2Float (extract v_10603 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10595 32 64) 24 8) (MInt2Float (extract v_10599 32 64) 24 8)) (MInt2Float (extract v_10603 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10595 64 96) 24 8) (MInt2Float (extract v_10599 64 96) 24 8)) (MInt2Float (extract v_10603 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10595 96 128) 24 8) (MInt2Float (extract v_10599 96 128) 24 8)) (MInt2Float (extract v_10603 96 128) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10595 128 160) 24 8) (MInt2Float (extract v_10599 128 160) 24 8)) (MInt2Float (extract v_10603 128 160) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10595 160 192) 24 8) (MInt2Float (extract v_10599 160 192) 24 8)) (MInt2Float (extract v_10603 160 192) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10595 192 224) 24 8) (MInt2Float (extract v_10599 192 224) 24 8)) (MInt2Float (extract v_10603 192 224) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10595 224 256) 24 8) (MInt2Float (extract v_10599 224 256) 24 8)) (MInt2Float (extract v_10603 224 256) 24 8)) 32))))));
      pure ()
    pat_end
