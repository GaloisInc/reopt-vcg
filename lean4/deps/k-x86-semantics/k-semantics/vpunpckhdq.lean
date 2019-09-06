def vpunpckhdq1 : instruction :=
  definst "vpunpckhdq" $ do
    pattern fun (v_2693 : reg (bv 128)) (v_2694 : reg (bv 128)) (v_2695 : reg (bv 128)) => do
      v_6206 <- getRegister v_2693;
      v_6208 <- getRegister v_2694;
      setRegister (lhs.of_reg v_2695) (concat (concat (extract v_6206 0 32) (extract v_6208 0 32)) (concat (extract v_6206 32 64) (extract v_6208 32 64)));
      pure ()
    pat_end;
    pattern fun (v_2704 : reg (bv 256)) (v_2705 : reg (bv 256)) (v_2706 : reg (bv 256)) => do
      v_6221 <- getRegister v_2704;
      v_6223 <- getRegister v_2705;
      setRegister (lhs.of_reg v_2706) (concat (concat (extract v_6221 0 32) (extract v_6223 0 32)) (concat (concat (extract v_6221 32 64) (extract v_6223 32 64)) (concat (concat (extract v_6221 128 160) (extract v_6223 128 160)) (concat (extract v_6221 160 192) (extract v_6223 160 192)))));
      pure ()
    pat_end;
    pattern fun (v_2687 : Mem) (v_2688 : reg (bv 128)) (v_2689 : reg (bv 128)) => do
      v_12288 <- evaluateAddress v_2687;
      v_12289 <- load v_12288 16;
      v_12291 <- getRegister v_2688;
      setRegister (lhs.of_reg v_2689) (concat (concat (extract v_12289 0 32) (extract v_12291 0 32)) (concat (extract v_12289 32 64) (extract v_12291 32 64)));
      pure ()
    pat_end;
    pattern fun (v_2698 : Mem) (v_2699 : reg (bv 256)) (v_2700 : reg (bv 256)) => do
      v_12299 <- evaluateAddress v_2698;
      v_12300 <- load v_12299 32;
      v_12302 <- getRegister v_2699;
      setRegister (lhs.of_reg v_2700) (concat (concat (extract v_12300 0 32) (extract v_12302 0 32)) (concat (concat (extract v_12300 32 64) (extract v_12302 32 64)) (concat (concat (extract v_12300 128 160) (extract v_12302 128 160)) (concat (extract v_12300 160 192) (extract v_12302 160 192)))));
      pure ()
    pat_end
