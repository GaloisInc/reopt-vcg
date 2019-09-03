def vfmaddsub213ps1 : instruction :=
  definst "vfmaddsub213ps" $ do
    pattern fun (v_2682 : reg (bv 128)) (v_2683 : reg (bv 128)) (v_2684 : reg (bv 128)) => do
      v_5046 <- getRegister v_2683;
      v_5049 <- getRegister v_2684;
      v_5053 <- getRegister v_2682;
      setRegister (lhs.of_reg v_2684) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5046 0 32) 24 8) (MInt2Float (extract v_5049 0 32) 24 8)) (MInt2Float (extract v_5053 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5046 32 64) 24 8) (MInt2Float (extract v_5049 32 64) 24 8)) (MInt2Float (extract v_5053 32 64) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5046 64 96) 24 8) (MInt2Float (extract v_5049 64 96) 24 8)) (MInt2Float (extract v_5053 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5046 96 128) 24 8) (MInt2Float (extract v_5049 96 128) 24 8)) (MInt2Float (extract v_5053 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2694 : reg (bv 256)) (v_2695 : reg (bv 256)) (v_2696 : reg (bv 256)) => do
      v_5094 <- getRegister v_2695;
      v_5097 <- getRegister v_2696;
      v_5101 <- getRegister v_2694;
      setRegister (lhs.of_reg v_2696) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5094 0 32) 24 8) (MInt2Float (extract v_5097 0 32) 24 8)) (MInt2Float (extract v_5101 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5094 32 64) 24 8) (MInt2Float (extract v_5097 32 64) 24 8)) (MInt2Float (extract v_5101 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5094 64 96) 24 8) (MInt2Float (extract v_5097 64 96) 24 8)) (MInt2Float (extract v_5101 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5094 96 128) 24 8) (MInt2Float (extract v_5097 96 128) 24 8)) (MInt2Float (extract v_5101 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5094 128 160) 24 8) (MInt2Float (extract v_5097 128 160) 24 8)) (MInt2Float (extract v_5101 128 160) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5094 160 192) 24 8) (MInt2Float (extract v_5097 160 192) 24 8)) (MInt2Float (extract v_5101 160 192) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5094 192 224) 24 8) (MInt2Float (extract v_5097 192 224) 24 8)) (MInt2Float (extract v_5101 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5094 224 256) 24 8) (MInt2Float (extract v_5097 224 256) 24 8)) (MInt2Float (extract v_5101 224 256) 24 8)) 32)))));
      pure ()
    pat_end;
    pattern fun (v_2679 : Mem) (v_2677 : reg (bv 128)) (v_2678 : reg (bv 128)) => do
      v_10961 <- getRegister v_2677;
      v_10964 <- getRegister v_2678;
      v_10968 <- evaluateAddress v_2679;
      v_10969 <- load v_10968 16;
      setRegister (lhs.of_reg v_2678) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10961 0 32) 24 8) (MInt2Float (extract v_10964 0 32) 24 8)) (MInt2Float (extract v_10969 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10961 32 64) 24 8) (MInt2Float (extract v_10964 32 64) 24 8)) (MInt2Float (extract v_10969 32 64) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10961 64 96) 24 8) (MInt2Float (extract v_10964 64 96) 24 8)) (MInt2Float (extract v_10969 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10961 96 128) 24 8) (MInt2Float (extract v_10964 96 128) 24 8)) (MInt2Float (extract v_10969 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2688 : Mem) (v_2689 : reg (bv 256)) (v_2690 : reg (bv 256)) => do
      v_11005 <- getRegister v_2689;
      v_11008 <- getRegister v_2690;
      v_11012 <- evaluateAddress v_2688;
      v_11013 <- load v_11012 32;
      setRegister (lhs.of_reg v_2690) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11005 0 32) 24 8) (MInt2Float (extract v_11008 0 32) 24 8)) (MInt2Float (extract v_11013 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11005 32 64) 24 8) (MInt2Float (extract v_11008 32 64) 24 8)) (MInt2Float (extract v_11013 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11005 64 96) 24 8) (MInt2Float (extract v_11008 64 96) 24 8)) (MInt2Float (extract v_11013 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11005 96 128) 24 8) (MInt2Float (extract v_11008 96 128) 24 8)) (MInt2Float (extract v_11013 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11005 128 160) 24 8) (MInt2Float (extract v_11008 128 160) 24 8)) (MInt2Float (extract v_11013 128 160) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11005 160 192) 24 8) (MInt2Float (extract v_11008 160 192) 24 8)) (MInt2Float (extract v_11013 160 192) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11005 192 224) 24 8) (MInt2Float (extract v_11008 192 224) 24 8)) (MInt2Float (extract v_11013 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11005 224 256) 24 8) (MInt2Float (extract v_11008 224 256) 24 8)) (MInt2Float (extract v_11013 224 256) 24 8)) 32)))));
      pure ()
    pat_end
