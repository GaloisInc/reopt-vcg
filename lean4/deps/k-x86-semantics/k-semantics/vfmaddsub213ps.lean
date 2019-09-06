def vfmaddsub213ps1 : instruction :=
  definst "vfmaddsub213ps" $ do
    pattern fun (v_2771 : reg (bv 128)) (v_2772 : reg (bv 128)) (v_2773 : reg (bv 128)) => do
      v_5140 <- getRegister v_2772;
      v_5143 <- getRegister v_2773;
      v_5147 <- getRegister v_2771;
      setRegister (lhs.of_reg v_2773) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5140 0 32) 24 8) (MInt2Float (extract v_5143 0 32) 24 8)) (MInt2Float (extract v_5147 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5140 32 64) 24 8) (MInt2Float (extract v_5143 32 64) 24 8)) (MInt2Float (extract v_5147 32 64) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5140 64 96) 24 8) (MInt2Float (extract v_5143 64 96) 24 8)) (MInt2Float (extract v_5147 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5140 96 128) 24 8) (MInt2Float (extract v_5143 96 128) 24 8)) (MInt2Float (extract v_5147 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2785 : reg (bv 256)) (v_2786 : reg (bv 256)) (v_2787 : reg (bv 256)) => do
      v_5188 <- getRegister v_2786;
      v_5191 <- getRegister v_2787;
      v_5195 <- getRegister v_2785;
      setRegister (lhs.of_reg v_2787) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5188 0 32) 24 8) (MInt2Float (extract v_5191 0 32) 24 8)) (MInt2Float (extract v_5195 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5188 32 64) 24 8) (MInt2Float (extract v_5191 32 64) 24 8)) (MInt2Float (extract v_5195 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5188 64 96) 24 8) (MInt2Float (extract v_5191 64 96) 24 8)) (MInt2Float (extract v_5195 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5188 96 128) 24 8) (MInt2Float (extract v_5191 96 128) 24 8)) (MInt2Float (extract v_5195 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5188 128 160) 24 8) (MInt2Float (extract v_5191 128 160) 24 8)) (MInt2Float (extract v_5195 128 160) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5188 160 192) 24 8) (MInt2Float (extract v_5191 160 192) 24 8)) (MInt2Float (extract v_5195 160 192) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5188 192 224) 24 8) (MInt2Float (extract v_5191 192 224) 24 8)) (MInt2Float (extract v_5195 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5188 224 256) 24 8) (MInt2Float (extract v_5191 224 256) 24 8)) (MInt2Float (extract v_5195 224 256) 24 8)) 32)))));
      pure ()
    pat_end;
    pattern fun (v_2768 : Mem) (v_2766 : reg (bv 128)) (v_2767 : reg (bv 128)) => do
      v_11072 <- getRegister v_2766;
      v_11075 <- getRegister v_2767;
      v_11079 <- evaluateAddress v_2768;
      v_11080 <- load v_11079 16;
      setRegister (lhs.of_reg v_2767) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11072 0 32) 24 8) (MInt2Float (extract v_11075 0 32) 24 8)) (MInt2Float (extract v_11080 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11072 32 64) 24 8) (MInt2Float (extract v_11075 32 64) 24 8)) (MInt2Float (extract v_11080 32 64) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11072 64 96) 24 8) (MInt2Float (extract v_11075 64 96) 24 8)) (MInt2Float (extract v_11080 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11072 96 128) 24 8) (MInt2Float (extract v_11075 96 128) 24 8)) (MInt2Float (extract v_11080 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2777 : Mem) (v_2780 : reg (bv 256)) (v_2781 : reg (bv 256)) => do
      v_11116 <- getRegister v_2780;
      v_11119 <- getRegister v_2781;
      v_11123 <- evaluateAddress v_2777;
      v_11124 <- load v_11123 32;
      setRegister (lhs.of_reg v_2781) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11116 0 32) 24 8) (MInt2Float (extract v_11119 0 32) 24 8)) (MInt2Float (extract v_11124 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11116 32 64) 24 8) (MInt2Float (extract v_11119 32 64) 24 8)) (MInt2Float (extract v_11124 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11116 64 96) 24 8) (MInt2Float (extract v_11119 64 96) 24 8)) (MInt2Float (extract v_11124 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11116 96 128) 24 8) (MInt2Float (extract v_11119 96 128) 24 8)) (MInt2Float (extract v_11124 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11116 128 160) 24 8) (MInt2Float (extract v_11119 128 160) 24 8)) (MInt2Float (extract v_11124 128 160) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11116 160 192) 24 8) (MInt2Float (extract v_11119 160 192) 24 8)) (MInt2Float (extract v_11124 160 192) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11116 192 224) 24 8) (MInt2Float (extract v_11119 192 224) 24 8)) (MInt2Float (extract v_11124 192 224) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11116 224 256) 24 8) (MInt2Float (extract v_11119 224 256) 24 8)) (MInt2Float (extract v_11124 224 256) 24 8)) 32)))));
      pure ()
    pat_end
