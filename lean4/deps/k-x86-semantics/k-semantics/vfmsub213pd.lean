def vfmsub213pd1 : instruction :=
  definst "vfmsub213pd" $ do
    pattern fun (v_2814 : reg (bv 128)) (v_2815 : reg (bv 128)) (v_2816 : reg (bv 128)) => do
      v_5646 <- getRegister v_2815;
      v_5649 <- getRegister v_2816;
      v_5653 <- getRegister v_2814;
      v_5657 <- eval (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5646 0 64) 53 11) (MInt2Float (extract v_5649 0 64) 53 11)) (MInt2Float (extract v_5653 0 64) 53 11)) 64);
      setRegister (lhs.of_reg v_2816) (concat (concat (extract v_5657 0 56) (extract v_5657 56 64)) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5646 64 128) 53 11) (MInt2Float (extract v_5649 64 128) 53 11)) (MInt2Float (extract v_5653 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2826 : reg (bv 256)) (v_2827 : reg (bv 256)) (v_2828 : reg (bv 256)) => do
      v_5677 <- getRegister v_2827;
      v_5680 <- getRegister v_2828;
      v_5684 <- getRegister v_2826;
      setRegister (lhs.of_reg v_2828) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5677 0 64) 53 11) (MInt2Float (extract v_5680 0 64) 53 11)) (MInt2Float (extract v_5684 0 64) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5677 64 128) 53 11) (MInt2Float (extract v_5680 64 128) 53 11)) (MInt2Float (extract v_5684 64 128) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5677 128 192) 53 11) (MInt2Float (extract v_5680 128 192) 53 11)) (MInt2Float (extract v_5684 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5677 192 256) 53 11) (MInt2Float (extract v_5680 192 256) 53 11)) (MInt2Float (extract v_5684 192 256) 53 11)) 64))));
      pure ()
    pat_end;
    pattern fun (v_2811 : Mem) (v_2809 : reg (bv 128)) (v_2810 : reg (bv 128)) => do
      v_11511 <- getRegister v_2809;
      v_11514 <- getRegister v_2810;
      v_11518 <- evaluateAddress v_2811;
      v_11519 <- load v_11518 16;
      v_11523 <- eval (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11511 0 64) 53 11) (MInt2Float (extract v_11514 0 64) 53 11)) (MInt2Float (extract v_11519 0 64) 53 11)) 64);
      setRegister (lhs.of_reg v_2810) (concat (concat (extract v_11523 0 56) (extract v_11523 56 64)) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11511 64 128) 53 11) (MInt2Float (extract v_11514 64 128) 53 11)) (MInt2Float (extract v_11519 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2820 : Mem) (v_2821 : reg (bv 256)) (v_2822 : reg (bv 256)) => do
      v_11538 <- getRegister v_2821;
      v_11541 <- getRegister v_2822;
      v_11545 <- evaluateAddress v_2820;
      v_11546 <- load v_11545 32;
      setRegister (lhs.of_reg v_2822) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11538 0 64) 53 11) (MInt2Float (extract v_11541 0 64) 53 11)) (MInt2Float (extract v_11546 0 64) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11538 64 128) 53 11) (MInt2Float (extract v_11541 64 128) 53 11)) (MInt2Float (extract v_11546 64 128) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11538 128 192) 53 11) (MInt2Float (extract v_11541 128 192) 53 11)) (MInt2Float (extract v_11546 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11538 192 256) 53 11) (MInt2Float (extract v_11541 192 256) 53 11)) (MInt2Float (extract v_11546 192 256) 53 11)) 64))));
      pure ()
    pat_end
