def psubw1 : instruction :=
  definst "psubw" $ do
    pattern fun (v_3207 : reg (bv 128)) (v_3208 : reg (bv 128)) => do
      v_8604 <- getRegister v_3208;
      v_8606 <- getRegister v_3207;
      setRegister (lhs.of_reg v_3208) (concat (sub (extract v_8604 0 16) (extract v_8606 0 16)) (concat (sub (extract v_8604 16 32) (extract v_8606 16 32)) (concat (sub (extract v_8604 32 48) (extract v_8606 32 48)) (concat (sub (extract v_8604 48 64) (extract v_8606 48 64)) (concat (sub (extract v_8604 64 80) (extract v_8606 64 80)) (concat (sub (extract v_8604 80 96) (extract v_8606 80 96)) (concat (sub (extract v_8604 96 112) (extract v_8606 96 112)) (sub (extract v_8604 112 128) (extract v_8606 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_3204 : Mem) (v_3203 : reg (bv 128)) => do
      v_15064 <- getRegister v_3203;
      v_15066 <- evaluateAddress v_3204;
      v_15067 <- load v_15066 16;
      setRegister (lhs.of_reg v_3203) (concat (sub (extract v_15064 0 16) (extract v_15067 0 16)) (concat (sub (extract v_15064 16 32) (extract v_15067 16 32)) (concat (sub (extract v_15064 32 48) (extract v_15067 32 48)) (concat (sub (extract v_15064 48 64) (extract v_15067 48 64)) (concat (sub (extract v_15064 64 80) (extract v_15067 64 80)) (concat (sub (extract v_15064 80 96) (extract v_15067 80 96)) (concat (sub (extract v_15064 96 112) (extract v_15067 96 112)) (sub (extract v_15064 112 128) (extract v_15067 112 128)))))))));
      pure ()
    pat_end
