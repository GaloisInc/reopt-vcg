def vmovshdup1 : instruction :=
  definst "vmovshdup" $ do
    pattern fun (v_3055 : reg (bv 128)) (v_3056 : reg (bv 128)) => do
      v_5070 <- getRegister v_3055;
      setRegister (lhs.of_reg v_3056) (concat (concat (extract v_5070 0 32) (extract v_5070 0 32)) (concat (extract v_5070 64 96) (extract v_5070 64 96)));
      pure ()
    pat_end;
    pattern fun (v_3064 : reg (bv 256)) (v_3065 : reg (bv 256)) => do
      v_5081 <- getRegister v_3064;
      setRegister (lhs.of_reg v_3065) (concat (concat (concat (extract v_5081 0 32) (extract v_5081 0 32)) (concat (extract v_5081 64 96) (extract v_5081 64 96))) (concat (concat (extract v_5081 128 160) (extract v_5081 128 160)) (concat (extract v_5081 192 224) (extract v_5081 192 224))));
      pure ()
    pat_end;
    pattern fun (v_3051 : Mem) (v_3052 : reg (bv 128)) => do
      v_10248 <- evaluateAddress v_3051;
      v_10249 <- load v_10248 16;
      setRegister (lhs.of_reg v_3052) (concat (concat (extract v_10249 0 32) (extract v_10249 0 32)) (concat (extract v_10249 64 96) (extract v_10249 64 96)));
      pure ()
    pat_end;
    pattern fun (v_3060 : Mem) (v_3061 : reg (bv 256)) => do
      v_10256 <- evaluateAddress v_3060;
      v_10257 <- load v_10256 32;
      setRegister (lhs.of_reg v_3061) (concat (concat (concat (extract v_10257 0 32) (extract v_10257 0 32)) (concat (extract v_10257 64 96) (extract v_10257 64 96))) (concat (concat (extract v_10257 128 160) (extract v_10257 128 160)) (concat (extract v_10257 192 224) (extract v_10257 192 224))));
      pure ()
    pat_end
